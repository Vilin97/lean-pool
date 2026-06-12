/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # LeakageEstimate.lean
  Leakage estimates for block-to-annulus energy transfer.
  Scaffolding notes: BlockDecomposition/leakage_estimate.md

  Dependencies: BlockDecomposition, LaplaceFactorial

  Public API:
  - `block_annulus_leakage`  (Theorem 5.7)
  - `total_leakage_bound`   (Theorem 5.8)
  - `eta_5_bound`           (Theorem 5.9)
-/
import LeanPool.PhaseRetrieval.Constant.Internal.BlockDecomposition
import LeanPool.PhaseRetrieval.Constant.Internal.LaplaceFactorial

/-! # LeakageEstimate -/


open MeasureTheory Real Finset Complex

noncomputable section

namespace FockSPR

/-! ## Private helpers -/

/-- `(fourier 1 t)^n = fourier n t` on `AddCircle T`. -/
private lemma fourier_pow (n : ℕ) (t : AddCircle T) :
    ((fourier 1 t : ℂ) ^ n : ℂ) = (fourier (n : ℤ) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← fourier_add]; push_cast; ring_nf

/-- `∫ fourier n = δ_{n,0}` w.r.t. normalized Haar. -/
private lemma integral_fourier (n : ℤ) :
    ∫ t : AddCircle T, (fourier n t : ℂ) ∂AddCircle.haarAddCircle =
    if n = 0 then 1 else 0 := by
  have h := fourierCoeff_fourier (T := T) 0
  have h1 := congr_fun h (-n)
  simp only [Pi.single_apply] at h1
  rw [fourierCoeff] at h1
  simp only [neg_neg, fourier_zero, smul_eq_mul, mul_one] at h1
  rw [h1]; simp [neg_eq_zero]

/-- Fourier orthogonality: `∫ fourier(m) · conj(fourier(n)) = δ_{m,n}`. -/
private lemma fourier_orthogonality (m n : ℤ) :
    ∫ t : AddCircle T, (fourier m t : ℂ) * (starRingEnd ℂ) (fourier n t : ℂ)
      ∂AddCircle.haarAddCircle =
    if m = n then 1 else 0 := by
  have key : ∀ t : AddCircle T,
      (fourier m t : ℂ) * (starRingEnd ℂ) (fourier n t : ℂ) = (fourier (m - n) t : ℂ) := by
    intro t; rw [← fourier_neg (n := n), ← fourier_add]; ring_nf
  simp_rw [key]; rw [integral_fourier]; simp [sub_eq_zero]

/-- `‖fourier n t‖ = 1` pointwise. -/
private lemma norm_fourier_eq_one (n : ℤ) (t : AddCircle T) :
    ‖(fourier n t : ℂ)‖ = 1 := by
  simp [fourier_apply, AddCircle.toCircle]

/-- Rewrite `blockPoly` at `r · fourier(1)(t)` as a Fourier series. -/
private lemma blockPoly_fourier_expansion {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ)
    (r : ℝ) (t : AddCircle T) :
    blockPoly a ℓ (↑r * (fourier 1 t : ℂ)) =
    ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
      then (a k * (r : ℂ) ^ (k.val + 1)) * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)
      else 0 := by
  unfold blockPoly
  congr 1; ext k; split_ifs with h
  · have : (↑r * (fourier 1 t : ℂ)) ^ (k.val + 1) =
        (r : ℂ) ^ (k.val + 1) * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ) := by
      rw [mul_pow, ← fourier_pow]
    rw [this]; ring
  · rfl

/-! ## Private Lemma: Distance bound

For `n ∈ I_ℓ` and integer `j ≥ 0`:
  `dist(√(n + 1/2), [j, j+1]) ≥ (|j − ℓ| − 1)₊`

**Proof**: Since `r_n ∈ (ℓ, ℓ+1)` (Theorem 5.6):
- `j ≥ ℓ + 1`: `dist = j − r_n > j − (ℓ+1) = |j−ℓ| − 1`.
- `j ≤ ℓ − 1`: `dist = r_n − (j+1) > ℓ − (j+1) = |j−ℓ| − 1`.
- `j = ℓ`: `r_n ∈ (j, j+1) ⊂ [j,j+1]`, so `dist = 0 = (0−1)₊ = 0`.
-/
private lemma dist_peak_to_interval {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n ∈ freqBlock ℓ) (j : ℕ) :
    distToInterval (rStar n) j ≥ max ((j : ℤ) - ℓ - 1) (ℓ - j - 1) := by
  obtain ⟨hlo, hhi⟩ := monomial_peak_localization hℓ hn
  unfold distToInterval rStar at *
  push_cast
  simp only [le_max_iff, max_le_iff]
  by_cases hjl : j ≥ ℓ + 1
  · left; left
    constructor
    · linarith
    · have : (j : ℝ) ≥ ℓ + 1 := by exact_mod_cast hjl
      linarith
  · push Not at hjl
    by_cases hjl2 : j + 1 ≤ ℓ
    · left; right
      constructor
      · have : (j : ℝ) + 1 ≤ ℓ := by exact_mod_cast hjl2
        linarith
      · have : (j : ℝ) + 1 ≤ ℓ := by exact_mod_cast hjl2
        linarith
    · push Not at hjl2
      have hje : j = ℓ := by omega
      right; subst hje
      constructor <;> linarith

/-- `distToInterval` is always nonneg. -/
private lemma distToInterval_nonneg (x : ℝ) (j : ℕ) : 0 ≤ distToInterval x j := by
  unfold distToInterval; exact le_max_right _ _

/-- `distToInterval ≥ max(j - ℓ - 1, 0)` for `n ∈ I_ℓ`. -/
private lemma dist_peak_ge_max_zero {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n ∈ freqBlock ℓ) (j : ℕ) :
    distToInterval (rStar n) j ≥ max ((j : ℤ) - ℓ - 1) 0 := by
  have hdist := dist_peak_to_interval hℓ hn j
  have hnonneg := distToInterval_nonneg (rStar n) j
  -- From hdist: distToInterval ≥ max(j-ℓ-1, ℓ-j-1) ≥ j-ℓ-1
  -- From hnonneg: distToInterval ≥ 0
  -- Together: distToInterval ≥ max(j-ℓ-1, 0)
  simp only [ge_iff_le, Int.cast_max] at hdist ⊢
  exact max_le (le_trans (le_max_left _ _) hdist) (by exact_mod_cast hnonneg)

/-- `distToInterval ≥ max(max(j - ℓ - 1, ℓ - j - 1), 0)` for `n ∈ I_ℓ` (symmetric). -/
private lemma dist_peak_ge_symmetric {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n ∈ freqBlock ℓ) (j : ℕ) :
    distToInterval (rStar n) j ≥ max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 := by
  have hdist := dist_peak_to_interval hℓ hn j
  have hnonneg := distToInterval_nonneg (rStar n) j
  simp only [ge_iff_le, Int.cast_max] at hdist ⊢
  exact max_le hdist (by exact_mod_cast hnonneg)

/-- Circle Parseval: `∫ ‖blockPoly a ℓ (r·ζ)‖² d(haar)(ζ) = ∑_k [k+1 ∈ I_ℓ] ‖a_k‖² r^{2(k+1)}`.
This uses Fourier orthogonality: the monomials `fourier n` are orthonormal. -/
private lemma blockPoly_circle_norm_sq {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) (r : ℝ) :
    ∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
      ∂AddCircle.haarAddCircle =
    ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
      then ‖a k‖ ^ 2 * (r : ℝ) ^ (2 * (k.val + 1)) else 0 := by
  -- Define coefficients and rewrite blockPoly as Fourier series
  set c : Fin D → ℂ := fun k =>
    if (k.val + 1) ∈ freqBlock ℓ then a k * (r : ℂ) ^ (k.val + 1) else 0 with hc_def
  have hbp : ∀ t : AddCircle T,
      blockPoly a ℓ (↑r * (fourier 1 t : ℂ)) =
      ∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ) := by
    intro t; rw [blockPoly_fourier_expansion]
    congr 1; ext k; simp only [hc_def]; split_ifs <;> simp
  simp_rw [hbp]
  -- The RHS can be rewritten in terms of ‖c k‖
  suffices h : ∀ k : Fin D,
      (if (k.val + 1) ∈ freqBlock ℓ then ‖a k‖ ^ 2 * r ^ (2 * (k.val + 1)) else 0) =
      ‖c k‖ ^ 2 by
    simp_rw [h]
    -- Now need: ∫ ‖∑ c_k fourier(k+1)‖² = ∑ ‖c_k‖²
    -- Helper: continuous functions on AddCircle are integrable (compact + finite measure)
    have hci : ∀ (g : AddCircle T → ℂ), Continuous g → Integrable g AddCircle.haarAddCircle :=
      fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hfc : Continuous (fun t : AddCircle T =>
        ∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) :=
      continuous_finsetSum _ fun k _ => continuous_const.mul (fourier _).continuous
    -- Integrability for pairs
    have hint_pair : ∀ (k1 k2 : Fin D), Integrable (fun t : AddCircle T =>
        (c k1 * (starRingEnd ℂ) (c k2)) *
        ((fourier ((k1.val + 1 : ℕ) : ℤ) t : ℂ) *
         (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) t : ℂ)))
        AddCircle.haarAddCircle :=
      fun k1 k2 => hci _ (continuous_const.mul
        ((fourier _).continuous.mul (continuous_star.comp (fourier _).continuous)))
    -- Compute complex integral of f * conj f
    have hcx_int : ∫ t : AddCircle T,
        (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
        (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ))
        ∂AddCircle.haarAddCircle =
        ↑(∑ k : Fin D, ‖c k‖ ^ 2) := by
      -- Expand
      simp_rw [map_sum, Finset.mul_sum, Finset.sum_mul, map_mul]
      -- Rearrange each term
      simp_rw [show ∀ (k1 k2 : Fin D) (t : AddCircle T),
          c k1 * (fourier ((k1.val + 1 : ℕ) : ℤ) t : ℂ) *
          ((starRingEnd ℂ) (c k2) *
           (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) t : ℂ)) =
          (c k1 * (starRingEnd ℂ) (c k2)) *
          ((fourier ((k1.val + 1 : ℕ) : ℤ) t : ℂ) *
           (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) t : ℂ))
        from fun k1 k2 t => by ring]
      -- Exchange integral and double sum
      rw [integral_finsetSum _ (fun k2 _ =>
        integrable_finsetSum _ (fun k1 _ => hint_pair k1 k2))]
      simp_rw [integral_finsetSum _ (fun k1 _ => hint_pair k1 _)]
      -- Each term: const * ∫ fourier * conj(fourier)
      -- Each integral: ∫ const * (fourier * conj(fourier)) = const * ∫ (fourier * conj(fourier))
      -- = const * δ(k1, k2) by fourier_orthogonality
      -- Evaluate each integral and collapse
      have heval : ∀ (k1 k2 : Fin D),
          ∫ (a : AddCircle T),
            c k1 * (starRingEnd ℂ) (c k2) *
            ((fourier ((k1.val + 1 : ℕ) : ℤ) a : ℂ) *
             (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) a : ℂ))
          ∂AddCircle.haarAddCircle =
          if k1 = k2 then (↑(‖c k1‖ ^ 2) : ℂ) else 0 := by
        intro k1 k2
        have : ∫ (t : AddCircle T),
            c k1 * (starRingEnd ℂ) (c k2) *
            ((fourier ((k1.val + 1 : ℕ) : ℤ) t : ℂ) *
             (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) t : ℂ))
            ∂AddCircle.haarAddCircle =
            c k1 * (starRingEnd ℂ) (c k2) *
            ∫ (t : AddCircle T),
              (fourier ((k1.val + 1 : ℕ) : ℤ) t : ℂ) *
              (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) t : ℂ)
            ∂AddCircle.haarAddCircle :=
          MeasureTheory.integral_const_mul _ _
        rw [this, fourier_orthogonality]
        by_cases hkk : k1 = k2
        · subst hkk
          simp only [ite_true, mul_one, Complex.mul_conj']; push_cast; rfl
        · have hne : ¬((k1.val + 1 : ℕ) : ℤ) = ((k2.val + 1 : ℕ) : ℤ) := by
            push_cast; omega
          simp only [hne, ite_false, mul_zero, hkk]
      simp_rw [heval, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      push_cast; ring
    -- From complex integral to real integral:
    -- ‖f t‖² = re(f t * conj(f t)), so ∫ ‖f‖² = re(∫ f * conj f) = ∑ ‖c_k‖²
    have hfconj : ∀ t : AddCircle T,
        (‖∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)‖ ^ 2 : ℝ) =
        ((∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
         (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ))).re := by
      intro t; rw [Complex.mul_conj']; norm_cast
    conv_lhs => arg 2; ext t; rw [hfconj t]
    have hfci : Integrable (fun t : AddCircle T =>
        (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
        (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)))
        AddCircle.haarAddCircle :=
      hci _ (hfc.mul (continuous_star.comp hfc))
    -- ∫ re(g) = re(∫ g) for integrable g
    have key : ∫ (t : AddCircle T),
        ((∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
          (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ))).re
        ∂AddCircle.haarAddCircle =
      (∫ (t : AddCircle T),
        (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
        (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ))
        ∂AddCircle.haarAddCircle).re := by
      change (∫ (t : AddCircle T),
          RCLike.re ((∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
            (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)))
          ∂AddCircle.haarAddCircle) = _
      exact integral_re hfci
    rw [key, hcx_int]; norm_cast
  intro k; simp only [hc_def]
  split_ifs with h
  · -- Goal: ‖a k‖² * r^{2(k+1)} = ‖a k * (↑r)^{k+1}‖²
    rw [Complex.norm_mul, mul_pow, Complex.norm_pow, Complex.norm_real,
      Real.norm_eq_abs, ← pow_mul]
    congr 1
    rw [show (k.val + 1) * 2 = 2 * (k.val + 1) from by ring]
    exact (Even.pow_abs ⟨k.val + 1, by ring⟩ r).symm
  · simp

/-! ## Theorem 5.7: Block-to-annulus leakage (single block)

For `ℓ ≥ 1`, `j ≥ 0`, and `a : Fin D → ℂ` defining `U_ℓ`:

  `(1/π) ∫_{j ≤ |z| < j+1} |U_ℓ(z)|² exp(−|z|²) dm ≤
      exp(1/4) · exp(−(max(|j−ℓ|−1, 0))²) · fockNormSq(U_ℓ)`

**Proof**:
1. Circle orthogonality (Thm 5.4): decompose into radial integrals.
2. Corollary 2.10: bound each radial integral.
3. Theorem 5.6: locate `r_n` in `(ℓ, ℓ+1)`, bound distance.
4. Sum over `n ∈ I_ℓ`.
-/
theorem block_annulus_leakage {D : ℕ} (a : Fin D → ℂ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (j : ℕ) :
    2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
        ∂AddCircle.haarAddCircle) ≤
      Real.exp (1 / 4) *
        Real.exp (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2) *
        (∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
          then ‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ) else 0) := by
  -- Step 1: Substitute the circle Parseval identity
  simp_rw [blockPoly_circle_norm_sq]
  -- Step 2: Rewrite each radial integrand to factor per-k
  have integrand_eq : ∀ (r : ℝ),
      r * Real.exp (-r ^ 2) *
        (∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
          then ‖a k‖ ^ 2 * r ^ (2 * (k.val + 1)) else 0) =
      ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) else 0 := by
    intro r
    rw [Finset.mul_sum]
    congr 1; ext k; split_ifs with h
    · ring
    · simp
  simp_rw [integrand_eq]
  -- Step 3: Bound each radial integral using monomial_integral_bound
  -- For each k with k+1 ∈ I_ℓ:
  --   ∫ r^{2(k+1)+1} exp(-r²) ≤ exp(1/4) * (k+1)!/2 * exp(-dist(r_{k+1},[j,j+1])²)
  -- Then: ‖a_k‖² * ∫ ... ≤ ‖a_k‖² * exp(1/4) * (k+1)!/2 * exp(-max(j-ℓ-1,0)²)
  -- (using dist_peak_ge_max_zero)
  -- Note: 2 * ∑ (‖a_k‖² * exp(1/4) * (k+1)!/2 * exp(-d²))
  --      = exp(1/4) * exp(-d²) * ∑ ‖a_k‖² * (k+1)!

  -- Establish per-k bounds
  have hk_bound : ∀ k : Fin D, (k.val + 1) ∈ freqBlock ℓ →
      2 * (‖a k‖ ^ 2 * ∫ r in (j : ℝ)..(j + 1 : ℝ),
        r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) ≤
      Real.exp (1 / 4) * Real.exp (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2) *
        (‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ)) := by
    intro k hk
    have hn : 1 ≤ k.val + 1 := Nat.succ_le_succ (Nat.zero_le _)
    -- Apply monomial_integral_bound
    have hmib := monomial_integral_bound hn j
    -- hmib : ∫ r^{2*(k+1)+1} exp(-r²) ≤ exp(1/4) * (k+1)!/2 * exp(-dist²)
    -- Bound distance: dist(r_{k+1}, [j,j+1]) ≥ max(j-ℓ-1, 0)
    have hdist := dist_peak_ge_max_zero hℓ hk j
    -- exp(-dist²) ≤ exp(-max(j-ℓ-1,0)²)
    have hexp_mono : Real.exp (-(distToInterval (rStar (k.val + 1)) j) ^ 2) ≤
        Real.exp (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      have h0 : (0 : ℝ) ≤ (max ((j : ℤ) - ℓ - 1) 0 : ℤ) := by
        exact_mod_cast le_max_right ((j : ℤ) - ℓ - 1) 0
      exact pow_le_pow_left₀ h0 (by exact_mod_cast hdist) 2
    -- Now: 2 * ‖a_k‖² * ∫ ≤ 2 * ‖a_k‖² * exp(1/4) * (k+1)!/2 * exp(-max(...)²)
    --    = ‖a_k‖² * exp(1/4) * (k+1)! * exp(-max(...)²)
    --    = exp(1/4) * exp(-max(...)²) * (‖a_k‖² * (k+1)!)
    have hint_bound : ∫ r in (j : ℝ)..(j + 1 : ℝ),
        r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2) ≤
        Real.exp (1 / 4) * (Nat.factorial (k.val + 1) : ℝ) / 2 *
        Real.exp (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2) := by
      calc ∫ r in (j : ℝ)..(j + 1 : ℝ),
            r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)
        ≤ Real.exp (1 / 4) * (Nat.factorial (k.val + 1) : ℝ) / 2 *
            Real.exp (-(distToInterval (rStar (k.val + 1)) j) ^ 2) :=
          monomial_integral_bound hn j
        _ ≤ Real.exp (1 / 4) * (Nat.factorial (k.val + 1) : ℝ) / 2 *
            Real.exp (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hexp_mono
          apply div_nonneg
          · apply mul_nonneg (le_of_lt (Real.exp_pos _))
            exact_mod_cast (Nat.factorial_pos (k.val + 1)).le
          · norm_num
    -- Combine: 2 * ‖a_k‖² * ∫ ≤ exp(1/4) * exp(-d²) * ‖a_k‖² * (k+1)!
    nlinarith [sq_nonneg (‖a k‖), Real.exp_pos (1 / 4 : ℝ),
               Real.exp_pos (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2 : ℝ),
               Nat.factorial_pos (k.val + 1)]
  -- Step 4: Exchange integral and sum, then apply per-k bounds
  -- First, prove integrability of each summand
  have hint : ∀ k : Fin D, IntervalIntegrable
      (fun r : ℝ => if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) else 0)
      (volume : Measure ℝ) (j : ℝ) (j + 1 : ℝ) := by
    intro k
    by_cases h : (k.val + 1) ∈ freqBlock ℓ
    · simp only [h, ite_true]
      apply Continuous.intervalIntegrable
      exact continuous_const.mul ((continuous_pow _).mul
        (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))))
    · simp only [h, ite_false]
      exact intervalIntegrable_const
  -- Exchange integral and sum: ∫ ∑ f_k = ∑ ∫ f_k
  rw [intervalIntegral.integral_finsetSum (μ := volume) (fun k _ => hint k)]
  -- Pull the if outside each integral
  have hpull_if : ∀ k : Fin D,
      ∫ (r : ℝ) in (j : ℝ)..(j + 1 : ℝ),
        (if (k.val + 1) ∈ freqBlock ℓ
          then ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) else 0) =
      if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * ∫ (r : ℝ) in (j : ℝ)..(j + 1 : ℝ),
          r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)
        else 0 := by
    intro k
    split_ifs with h
    · rw [intervalIntegral.integral_const_mul]
    · simp
  simp_rw [hpull_if]
  -- Now: 2 * ∑_k [h] ‖a_k‖² * ∫ f_k ≤ exp(1/4) * exp(-d²) * ∑_k [h] ‖a_k‖² * (k+1)!
  rw [mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with h
  · exact hk_bound k h
  · simp

/-! ## Theorem 5.8: Total leakage bound

For `M ≥ 2`:

  `∑_j ∫_{A_j} |R_j|² dμ ≤ η_M · fockNormSq(U)`

where `η_M := 2 exp(1/4) ∑_{m ≥ M} exp(−m²)`.

**Proof**:
1. Orthogonality on annuli: `∫_{A_j} |R_j|² dμ = ∑_{|ℓ−j|>M} ∫_{A_j} |U_ℓ|² dμ`.
2. Apply Theorem 5.7 to each term.
3. Swap order of summation (Tonelli): `∑_j ∑_{|ℓ−j|>M} … ≤ ∑_ℓ fockNormSq(U_ℓ) · …`.
4. Inner sum: `∑_{|j−ℓ|>M} exp(−(|j−ℓ|−1)²) ≤ 2 ∑_{m≥M} exp(−m²)`.
5. Hence total `≤ η_M · fockNormSq(U)`.
-/

/-- The leakage coefficient `η_M = 2 exp(1/4) ∑_{m ≥ M}^∞ exp(−m²)`. -/
def etaCoeff (M : ℕ) (bound : ℕ) : ℝ :=
  2 * Real.exp (1 / 4) * ∑ m ∈ Finset.Icc M bound, Real.exp (-(m : ℝ) ^ 2)

/-! ### Helper: symmetric block_annulus_leakage -/

/-- Symmetric version of block_annulus_leakage using the full distance
`max(max(j−ℓ−1, ℓ−j−1), 0)` instead of just `max(j−ℓ−1, 0)`.
This is proved by repeating the per-monomial argument from block_annulus_leakage
but using `dist_peak_ge_symmetric` instead of `dist_peak_ge_max_zero`. -/
private lemma block_annulus_leakage_symmetric {D : ℕ} (a : Fin D → ℂ) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (j : ℕ) :
    2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
        ∂AddCircle.haarAddCircle) ≤
      Real.exp (1 / 4) *
        Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2) *
        (∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
          then ‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ) else 0) := by
  -- Substitute Parseval
  simp_rw [blockPoly_circle_norm_sq]
  -- Rewrite integrand
  have integrand_eq : ∀ (r : ℝ),
      r * Real.exp (-r ^ 2) *
        (∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
          then ‖a k‖ ^ 2 * r ^ (2 * (k.val + 1)) else 0) =
      ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) else 0 := by
    intro r; rw [Finset.mul_sum]; congr 1; ext k; split_ifs with h
    · ring
    · simp
  simp_rw [integrand_eq]
  -- Per-k bounds using dist_peak_ge_symmetric
  have hk_bound : ∀ k : Fin D, (k.val + 1) ∈ freqBlock ℓ →
      2 * (‖a k‖ ^ 2 * ∫ r in (j : ℝ)..(j + 1 : ℝ),
        r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) ≤
      Real.exp (1 / 4) *
        Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2) *
        (‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ)) := by
    intro k hk
    have hn : 1 ≤ k.val + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hdist := dist_peak_ge_symmetric hℓ hk j
    have hexp_mono : Real.exp (-(distToInterval (rStar (k.val + 1)) j) ^ 2) ≤
        Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2) := by
      apply Real.exp_le_exp.mpr; apply neg_le_neg
      have h0 : (0 : ℝ) ≤ (max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) := by
        exact_mod_cast le_max_right _ (0 : ℤ)
      exact pow_le_pow_left₀ h0 (by exact_mod_cast hdist) 2
    have hint_bound : ∫ r in (j : ℝ)..(j + 1 : ℝ),
        r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2) ≤
        Real.exp (1 / 4) * (Nat.factorial (k.val + 1) : ℝ) / 2 *
        Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2) := by
      calc ∫ r in (j : ℝ)..(j + 1 : ℝ),
            r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)
        ≤ Real.exp (1 / 4) * (Nat.factorial (k.val + 1) : ℝ) / 2 *
            Real.exp (-(distToInterval (rStar (k.val + 1)) j) ^ 2) :=
          monomial_integral_bound hn j
        _ ≤ Real.exp (1 / 4) * (Nat.factorial (k.val + 1) : ℝ) / 2 *
            Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hexp_mono
          apply div_nonneg
          · apply mul_nonneg (le_of_lt (Real.exp_pos _))
            exact_mod_cast (Nat.factorial_pos (k.val + 1)).le
          · norm_num
    nlinarith [sq_nonneg (‖a k‖), Real.exp_pos (1 / 4 : ℝ),
               Real.exp_pos (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2 : ℝ),
               Nat.factorial_pos (k.val + 1)]
  -- Exchange integral and sum
  have hint : ∀ k : Fin D, IntervalIntegrable
      (fun r : ℝ => if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) else 0)
      (volume : Measure ℝ) (j : ℝ) (j + 1 : ℝ) := by
    intro k; by_cases h : (k.val + 1) ∈ freqBlock ℓ
    · simp only [h, ite_true]; apply Continuous.intervalIntegrable
      exact continuous_const.mul ((continuous_pow _).mul
        (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))))
    · simp only [h, ite_false]; exact intervalIntegrable_const
  rw [intervalIntegral.integral_finsetSum (μ := volume) (fun k _ => hint k)]
  have hpull_if : ∀ k : Fin D,
      ∫ (r : ℝ) in (j : ℝ)..(j + 1 : ℝ),
        (if (k.val + 1) ∈ freqBlock ℓ
          then ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) else 0) =
      if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * ∫ (r : ℝ) in (j : ℝ)..(j + 1 : ℝ),
          r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)
        else 0 := by
    intro k; split_ifs with h
    · rw [intervalIntegral.integral_const_mul]
    · simp
  simp_rw [hpull_if]
  rw [mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _; split_ifs with h
  · exact hk_bound k h
  · simp

/-! ### Helper: remainder ≤ far blocks (annulus level)

This combines two steps:
1. Circle Parseval: ‖R_j(r·ζ)‖²_{L²} = ∑_{k not near} ‖a_k‖² r^{2(k+1)}
2. Block grouping: ∑_{k not near} ≤ ∑_{far ℓ} ∑_{k∈I_ℓ} = ∑_{far ℓ} ‖U_ℓ(r·ζ)‖²
   (using blocks_cover and blocks_disjoint)
These give a pointwise (in r) bound on the circle norm.
The annulus-level bound follows by integrating against r exp(-r²) ≥ 0
and exchanging sum and integral (finite sum of continuous functions). -/

/-- `polyEval a z = ∑ ℓ ∈ Icc 1 Λ, blockPoly a ℓ z`: the polynomial decomposes into blocks. -/
private lemma polyEval_eq_sum_blockPoly {D : ℕ} (a : Fin D → ℂ) (z : ℂ) :
    polyEval a z = ∑ ℓ ∈ Finset.Icc 1 (maxBlockIndex D), blockPoly a ℓ z := by
  unfold polyEval blockPoly
  -- LHS = ∑_k a_k z^{k+1}
  -- RHS = ∑_ℓ ∑_k [k+1 ∈ I_ℓ] a_k z^{k+1}
  -- Swap sums: = ∑_k (∑_ℓ [k+1 ∈ I_ℓ]) a_k z^{k+1}
  -- By blocks_cover+blocks_disjoint, ∑_ℓ [k+1 ∈ I_ℓ] = 1 for each k
  rw [Finset.sum_comm]
  congr 1; ext k
  simp_rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  -- Goal: a k * z ^ (k+1) = ∑_{ℓ ∈ filter(k+1 ∈ I_ℓ) Icc 1 Λ} a k * z ^ (k+1)
  rw [Finset.sum_const]
  -- Need: card of filter = 1, then 1 • x = x
  suffices hcard :
      ((Finset.Icc 1 (maxBlockIndex D)).filter
        (fun ℓ => (k.val + 1) ∈ freqBlock ℓ)).card = 1 by
    rw [hcard]; simp
  -- By blocks_cover, k+1 is in some block; by blocks_disjoint, it's in at most one
  have hk1 : 1 ≤ k.val + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hkD : k.val + 1 ≤ D := Nat.succ_le_of_lt k.isLt
  obtain ⟨ℓ, hℓ1, hℓmem⟩ := blocks_cover D (k.val + 1) hk1 hkD
  rw [Finset.card_eq_one]
  refine ⟨ℓ, ?_⟩
  ext ℓ'
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · intro ⟨⟨hℓ'1, hℓ'Λ⟩, hℓ'mem⟩
    by_contra hne
    have hdisj := blocks_disjoint hℓ1 hℓ'1 (Ne.symm hne)
    exact Finset.disjoint_left.mp hdisj hℓmem hℓ'mem
  · intro h; rw [h]
    refine ⟨⟨hℓ1, ?_⟩, hℓmem⟩
    unfold maxBlockIndex
    rw [Nat.le_sqrt]
    have hfb : k.val + 1 ∈ freqBlock ℓ := hℓmem
    unfold freqBlock at hfb
    simp only [Finset.mem_Icc] at hfb
    have : k.val + 1 ≤ D := Nat.succ_le_of_lt k.isLt
    calc ℓ * ℓ = ℓ ^ 2 := by ring
      _ ≤ k.val + 1 := hfb.1
      _ ≤ D := this

/-- `remainderPoly a M j z = ∑_{far ℓ} blockPoly a ℓ z` where "far" means
`j + M < ℓ ∨ ℓ + M < j`. -/
private lemma remainderPoly_eq_sum_far_blocks {D : ℕ} (a : Fin D → ℂ) (M : ℕ)
    (j : ℕ) (z : ℂ) :
    remainderPoly a M j z =
    ∑ ℓ ∈ (Finset.Icc 1 (maxBlockIndex D)).filter (fun ℓ => j + M < ℓ ∨ ℓ + M < j),
      blockPoly a ℓ z := by
  unfold remainderPoly localPoly
  rw [polyEval_eq_sum_blockPoly]
  -- polyEval - localPoly = ∑_{all ℓ} block - ∑_{near ℓ} block = ∑_{far ℓ} block
  -- Key: near set = complement of far set within Icc 1 Λ
  have hnear_eq : Finset.Icc (max 1 (j - M)) (min (maxBlockIndex D) (j + M)) =
      (Finset.Icc 1 (maxBlockIndex D)).filter (fun ℓ => ¬(j + M < ℓ ∨ ℓ + M < j)) := by
    ext ℓ; simp only [Finset.mem_Icc, Finset.mem_filter, not_or, not_lt]; omega
  rw [hnear_eq]
  -- Now: ∑_all - ∑_{not far} = ∑_far
  have h := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 (maxBlockIndex D))
    (fun ℓ => j + M < ℓ ∨ ℓ + M < j) (fun ℓ => blockPoly a ℓ z)
  -- h : ∑_far + ∑_{not far} = ∑_all
  -- Goal: ∑_all - ∑_{not far} = ∑_far
  rw [← h]; ring

/-- Pythagorean identity for block polynomials on circles: for pairwise distinct blocks
`ℓ ≥ 1`, `∫ ‖∑ U_ℓ‖² = ∑ ∫ ‖U_ℓ‖²` by orthogonality (blocks_orthogonal_circle). -/
private lemma circle_norm_sq_sum_blocks {D : ℕ} (a : Fin D → ℂ)
    (S : Finset ℕ) (hS : ∀ ℓ ∈ S, 1 ≤ ℓ) (r : ℝ) (hr : 0 ≤ r) :
    ∫ t : AddCircle T, ‖∑ ℓ ∈ S, blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
      ∂AddCircle.haarAddCircle =
    ∑ ℓ ∈ S, ∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
      ∂AddCircle.haarAddCircle := by
  -- Helper: continuous functions on AddCircle are integrable
  have hci : ∀ (g : AddCircle T → ℂ), Continuous g → Integrable g AddCircle.haarAddCircle :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcont_block : ∀ ℓ, Continuous (fun t : AddCircle T =>
      blockPoly a ℓ (↑r * (fourier 1 t : ℂ))) := by
    intro ℓ; unfold blockPoly
    apply continuous_finsetSum; intro k _
    split_ifs
    · exact continuous_const.mul ((continuous_const.mul (fourier _).continuous).pow _)
    · exact continuous_const
  have hcont_sum : Continuous (fun t : AddCircle T =>
      ∑ ℓ ∈ S, blockPoly a ℓ (↑r * (fourier 1 t : ℂ))) :=
    continuous_finsetSum _ fun ℓ _ => hcont_block ℓ
  have hint_pair : ∀ (ℓ₁ ℓ₂ : ℕ), Integrable (fun t : AddCircle T =>
      blockPoly a ℓ₁ (↑r * (fourier 1 t : ℂ)) *
      (starRingEnd ℂ) (blockPoly a ℓ₂ (↑r * (fourier 1 t : ℂ))))
      AddCircle.haarAddCircle :=
    fun ℓ₁ ℓ₂ => hci _ ((hcont_block ℓ₁).mul (continuous_star.comp (hcont_block ℓ₂)))
  -- ‖f‖² = re(f * conj f)
  have hnorm_sq : ∀ (f : ℂ), (‖f‖ ^ 2 : ℝ) = (f * starRingEnd ℂ f).re := by
    intro f; rw [Complex.mul_conj']; norm_cast
  -- Cross terms vanish
  have hcross : ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ →
      ∫ t : AddCircle T,
        blockPoly a ℓ₁ (↑r * (fourier 1 t : ℂ)) *
        (starRingEnd ℂ) (blockPoly a ℓ₂ (↑r * (fourier 1 t : ℂ)))
        ∂AddCircle.haarAddCircle = 0 :=
    fun ℓ₁ hℓ₁ ℓ₂ hℓ₂ hne => blocks_orthogonal_circle a (hS ℓ₁ hℓ₁) (hS ℓ₂ hℓ₂) hne r hr
  -- LHS: rewrite ‖∑ f_ℓ‖² = re((∑ f_ℓ) * conj(∑ f_ℓ))
  conv_lhs => arg 2; ext t; rw [hnorm_sq]
  rw [show ∫ t : AddCircle T,
      ((∑ ℓ ∈ S, blockPoly a ℓ (↑r * (fourier 1 t : ℂ))) *
       starRingEnd ℂ (∑ ℓ ∈ S, blockPoly a ℓ (↑r * (fourier 1 t : ℂ)))).re
      ∂AddCircle.haarAddCircle =
      (∫ t : AddCircle T,
       (∑ ℓ ∈ S, blockPoly a ℓ (↑r * (fourier 1 t : ℂ))) *
       starRingEnd ℂ (∑ ℓ ∈ S, blockPoly a ℓ (↑r * (fourier 1 t : ℂ)))
       ∂AddCircle.haarAddCircle).re from by
    change (∫ t : AddCircle T,
        RCLike.re ((∑ ℓ ∈ S, blockPoly a ℓ (↑r * (fourier 1 t : ℂ))) *
          starRingEnd ℂ (∑ ℓ ∈ S, blockPoly a ℓ (↑r * (fourier 1 t : ℂ))))
        ∂AddCircle.haarAddCircle) = _
    exact integral_re (hci _ (hcont_sum.mul (continuous_star.comp hcont_sum)))]
  -- Expand product of sums: conj distributes, then multiply sums
  -- Work with the complex integral first, then take .re
  -- Goal: (∫ t, (∑ f_ℓ) * conj(∑ f_ℓ) ∂haar).re = ∑_ℓ ∫ ‖f_ℓ‖²
  -- Step B1: Exchange integral and double sum (complex-valued)
  have step1 : ∫ t : AddCircle T,
      (∑ ℓ₁ ∈ S, blockPoly a ℓ₁ (↑r * (fourier 1 t : ℂ))) *
      starRingEnd ℂ (∑ ℓ₂ ∈ S, blockPoly a ℓ₂ (↑r * (fourier 1 t : ℂ)))
      ∂AddCircle.haarAddCircle =
      ∑ ℓ ∈ S, ∫ t : AddCircle T,
        blockPoly a ℓ (↑r * (fourier 1 t : ℂ)) *
        (starRingEnd ℂ) (blockPoly a ℓ (↑r * (fourier 1 t : ℂ)))
        ∂AddCircle.haarAddCircle := by
    -- Expand conj(∑) = ∑ conj, then distribute
    conv_lhs => arg 2; ext t; rw [map_sum]; rw [Finset.sum_mul]; arg 2; ext ℓ₁; rw [Finset.mul_sum]
    -- Exchange outer sum and integral
    rw [integral_finsetSum _ (fun ℓ₁ _ =>
      integrable_finsetSum _ (fun ℓ₂ _ => hint_pair ℓ₁ ℓ₂))]
    -- Exchange inner sum and integral for each ℓ₁
    simp_rw [integral_finsetSum _ (fun ℓ₂ _ => hint_pair _ ℓ₂)]
    -- Kill cross terms: for each ℓ₁, ∑_ℓ₂ ∫ f_ℓ₁ * conj(f_ℓ₂) = ∫ f_ℓ₁ * conj(f_ℓ₁)
    rw [Finset.sum_congr rfl (fun ℓ₁ hℓ₁ => Finset.sum_eq_single_of_mem ℓ₁ hℓ₁
      (fun ℓ₂ hℓ₂ hne => hcross ℓ₁ hℓ₁ ℓ₂ hℓ₂ (Ne.symm hne)))]
  rw [step1, Complex.re_sum]
  -- Now goal: ∑_ℓ (∫ f_ℓ * conj f_ℓ).re = ∑_ℓ ∫ ‖f_ℓ‖²
  congr 1; ext ℓ
  -- re(∫ f * conj f) = ∫ re(f * conj f) = ∫ ‖f‖²
  rw [show (∫ t : AddCircle T,
      blockPoly a ℓ (↑r * (fourier 1 t : ℂ)) *
      (starRingEnd ℂ) (blockPoly a ℓ (↑r * (fourier 1 t : ℂ)))
      ∂AddCircle.haarAddCircle).re =
      ∫ t : AddCircle T, (blockPoly a ℓ (↑r * (fourier 1 t : ℂ)) *
      (starRingEnd ℂ) (blockPoly a ℓ (↑r * (fourier 1 t : ℂ)))).re
      ∂AddCircle.haarAddCircle from by
    symm
    change (∫ t : AddCircle T,
        RCLike.re (blockPoly a ℓ (↑r * (fourier 1 t : ℂ)) *
          starRingEnd ℂ (blockPoly a ℓ (↑r * (fourier 1 t : ℂ))))
        ∂AddCircle.haarAddCircle) = _
    exact integral_re (hint_pair ℓ ℓ)]
  congr 1; ext t; rw [← hnorm_sq]

/-- Annulus-level bound: the remainder's annulus energy equals the sum of far block annulus
energies. -/
private lemma remainder_annulus_le_far_blocks {D : ℕ} (a : Fin D → ℂ) {M : ℕ}
    (_hM : 1 ≤ M) (j : ℕ) :
    2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, ‖remainderPoly a M j (↑r * (fourier 1 t : ℂ))‖ ^ 2
        ∂AddCircle.haarAddCircle) ≤
    ∑ ℓ ∈ Finset.Icc 1 (maxBlockIndex D),
      if (j + M < ℓ ∨ ℓ + M < j) then
        2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
          (∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
            ∂AddCircle.haarAddCircle)
      else 0 := by
  set S := (Finset.Icc 1 (maxBlockIndex D)).filter (fun ℓ => j + M < ℓ ∨ ℓ + M < j)
  have hS1 : ∀ ℓ ∈ S, 1 ≤ ℓ :=
    fun ℓ hℓ => (Finset.mem_Icc.mp (Finset.mem_filter.mp hℓ).1).1
  -- Step 1: Pointwise identity for circle norms using Pythagorean identity
  have hpw : ∀ r : ℝ, 0 ≤ r →
      ∫ t : AddCircle T, ‖remainderPoly a M j (↑r * (fourier 1 t : ℂ))‖ ^ 2
        ∂AddCircle.haarAddCircle =
      ∑ ℓ ∈ S, ∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
        ∂AddCircle.haarAddCircle := by
    intro r hr
    simp_rw [remainderPoly_eq_sum_far_blocks a M j]
    exact circle_norm_sq_sum_blocks a S hS1 r hr
  -- Step 2: Rewrite the integrand using the pointwise identity
  have heq : ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, ‖remainderPoly a M j (↑r * (fourier 1 t : ℂ))‖ ^ 2
        ∂AddCircle.haarAddCircle) =
      ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
      (∑ ℓ ∈ S, ∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
        ∂AddCircle.haarAddCircle) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le (show (j : ℝ) ≤ j + 1 by linarith)] at hr
    have hr0 : (0 : ℝ) ≤ r := le_trans (Nat.cast_nonneg j) hr.1
    dsimp only
    rw [hpw r hr0]
  rw [heq]
  -- Step 3: Distribute weight over the sum inside the integral
  have integrand_eq : ∀ r : ℝ,
      r * Real.exp (-r ^ 2) *
      (∑ ℓ ∈ S, ∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
        ∂AddCircle.haarAddCircle) =
      ∑ ℓ ∈ S, r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
          ∂AddCircle.haarAddCircle) :=
    fun r => Finset.mul_sum S _ (r * Real.exp (-r ^ 2))
  simp_rw [integrand_eq]
  -- Step 4: Exchange integral and sum (continuous functions on bounded interval)
  have hint : ∀ ℓ, IntervalIntegrable
      (fun r : ℝ => r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
          ∂AddCircle.haarAddCircle))
      (volume : Measure ℝ) (j : ℝ) (j + 1 : ℝ) := by
    intro ℓ
    apply Continuous.intervalIntegrable
    apply Continuous.mul
    · exact continuous_id.mul (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2)))
    · simp_rw [blockPoly_circle_norm_sq]
      apply continuous_finsetSum; intro k _
      split_ifs
      · exact continuous_const.mul (continuous_pow _)
      · exact continuous_const
  rw [intervalIntegral.integral_finsetSum (μ := volume) (fun ℓ _ => hint ℓ)]
  -- Step 5: Factor out 2 and convert filter to if-else
  rw [mul_sum]
  -- Convert RHS from if-else to filter sum
  rw [show ∑ ℓ ∈ Finset.Icc 1 (maxBlockIndex D),
      (if (j + M < ℓ ∨ ℓ + M < j) then
        2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
          (∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
            ∂AddCircle.haarAddCircle)
      else 0) =
      ∑ ℓ ∈ S, 2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
          (∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
            ∂AddCircle.haarAddCircle)
    from (Finset.sum_filter _ _).symm]

/-! ### Helper: inner sum bound -/

-- inner_sum_bound uses image/filter finset manipulations that need extra heartbeats
/-- For fixed ℓ (with ℓ ≤ J), the sum over "far" j of the exponential decay factor is bounded by
`2 · ∑_{m=M}^{J} exp(-m²)`. Split into right (j > ℓ+M) and left (j+M < ℓ) halves;
each half maps injectively into `Icc M J` via `m = j-ℓ-1` or `m = ℓ-j-1`. -/
private lemma inner_sum_bound (M J ℓ : ℕ) (hM : 2 ≤ M) (hℓJ : ℓ ≤ J) :
    ∑ j ∈ (Finset.range J).filter (fun j => j + M < ℓ ∨ ℓ + M < j),
      Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2) ≤
    2 * ∑ m ∈ Finset.Icc M J, Real.exp (-(m : ℝ) ^ 2) := by
  -- Split into disjoint right (ℓ + M < j) and left (j + M < ℓ) parts
  have hdisj : Disjoint
    ((Finset.range J).filter (fun j => ℓ + M < j))
    ((Finset.range J).filter (fun j => j + M < ℓ)) := by
    simp only [Finset.disjoint_filter]; intro j _ h1 h2; omega
  rw [show (Finset.range J).filter (fun j => j + M < ℓ ∨ ℓ + M < j) =
    ((Finset.range J).filter (fun j => ℓ + M < j)) ∪
    ((Finset.range J).filter (fun j => j + M < ℓ)) from by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]; tauto,
    Finset.sum_union hdisj, show (2 : ℝ) = 1 + 1 by norm_num, add_mul]
  apply add_le_add
  · -- Right half: j > ℓ + M, distance = j - ℓ - 1
    rw [one_mul]
    have hval : ∀ j ∈ (Finset.range J).filter (fun j => ℓ + M < j),
        Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2) =
        Real.exp (-(((fun j => j - ℓ - 1) j : ℕ) : ℝ) ^ 2) := by
      intro j hj; have hjf := (Finset.mem_filter.mp hj).2; congr 1
      rw [max_eq_left (show (ℓ : ℤ) - j - 1 ≤ (j : ℤ) - ℓ - 1 by omega),
          max_eq_left (show (0 : ℤ) ≤ (j : ℤ) - ℓ - 1 by omega)]
      simp only; rw [← show ((j - ℓ - 1 : ℕ) : ℤ) = (j : ℤ) - ℓ - 1 from by omega]
      push_cast; ring
    calc _ = ∑ j ∈ (Finset.range J).filter (fun j => ℓ + M < j),
          Real.exp (-(((fun j => j - ℓ - 1) j : ℕ) : ℝ) ^ 2) := Finset.sum_congr rfl hval
      _ = ∑ m ∈ ((Finset.range J).filter (fun j => ℓ + M < j)).image (fun j => j - ℓ - 1),
          Real.exp (-(m : ℝ) ^ 2) := by
        symm; apply Finset.sum_image; intro j1 hj1 j2 hj2 h
        have := (Finset.mem_filter.mp hj1).2; have := (Finset.mem_filter.mp hj2).2
        simp only at h; omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (fun m hm => by
            simp only [Finset.mem_image, Finset.mem_filter] at hm
            obtain ⟨j, ⟨hjR, hjf⟩, rfl⟩ := hm
            have := Finset.mem_range.mp hjR
            exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          (fun _ _ _ => le_of_lt (Real.exp_pos _))
  · -- Left half: j + M < ℓ, distance = ℓ - j - 1
    rw [one_mul]
    have hval : ∀ j ∈ (Finset.range J).filter (fun j => j + M < ℓ),
        Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2) =
        Real.exp (-(((fun j => ℓ - j - 1) j : ℕ) : ℝ) ^ 2) := by
      intro j hj; have hjf := (Finset.mem_filter.mp hj).2; congr 1
      rw [max_eq_right (show (j : ℤ) - ℓ - 1 ≤ (ℓ : ℤ) - j - 1 by omega),
          max_eq_left (show (0 : ℤ) ≤ (ℓ : ℤ) - j - 1 by omega)]
      simp only; rw [← show ((ℓ - j - 1 : ℕ) : ℤ) = (ℓ : ℤ) - j - 1 from by omega]
      push_cast; ring
    calc _ = ∑ j ∈ (Finset.range J).filter (fun j => j + M < ℓ),
          Real.exp (-(((fun j => ℓ - j - 1) j : ℕ) : ℝ) ^ 2) := Finset.sum_congr rfl hval
      _ = ∑ m ∈ ((Finset.range J).filter (fun j => j + M < ℓ)).image (fun j => ℓ - j - 1),
          Real.exp (-(m : ℝ) ^ 2) := by
        symm; apply Finset.sum_image; intro j1 hj1 j2 hj2 h
        have := (Finset.mem_filter.mp hj1).2; have := (Finset.mem_filter.mp hj2).2
        simp only at h; omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (fun m hm => by
            simp only [Finset.mem_image, Finset.mem_filter] at hm
            obtain ⟨j, ⟨hjR, hjf⟩, rfl⟩ := hm
            have := Finset.mem_range.mp hjR
            exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          (fun _ _ _ => le_of_lt (Real.exp_pos _))

/-- fockNormSq_block: the block Fock norm for block ℓ. -/
private def fockNormSqBlock {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) : ℝ :=
  ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
    then ‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ) else 0

/-- The block Fock norms are nonneg. -/
private lemma fockNormSqBlock_nonneg {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) :
    0 ≤ fockNormSqBlock a ℓ :=
  Finset.sum_nonneg fun k _ => by show 0 ≤ _; split_ifs <;> positivity

/-! ### Main theorem -/

theorem total_leakage_bound {D : ℕ} (a : Fin D → ℂ) {M : ℕ} (hM : 2 ≤ M) :
    ∀ ε > 0, ∃ bound, ∀ J ≥ bound,
    (∑ j ∈ Finset.range J,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, ‖remainderPoly a M j (↑r * (fourier 1 t : ℂ))‖ ^ 2
          ∂AddCircle.haarAddCircle)) ≤
    (etaCoeff M J + ε) * fockNormSq a := by
  intro ε hε
  use maxBlockIndex D
  intro J hJbound
  suffices h : (∑ j ∈ Finset.range J,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, ‖remainderPoly a M j (↑r * (fourier 1 t : ℂ))‖ ^ 2
          ∂AddCircle.haarAddCircle)) ≤
    etaCoeff M J * fockNormSq a by
    calc _ ≤ etaCoeff M J * fockNormSq a := h
      _ ≤ (etaCoeff M J + ε) * fockNormSq a := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · exact Finset.sum_nonneg fun k _ =>
            mul_nonneg (sq_nonneg _) (by exact_mod_cast (Nat.factorial_pos _).le)
  -- Main bound: ∑_j 2∫ r exp(-r²) ∫_circle ‖R_j‖² ≤ etaCoeff M J * fockNormSq a
  -- Step 1: Bound each j-summand.
  -- For each j, by remainder_le_far_blocks (pointwise in r) and monotonicity of the
  -- radial integral, we bound the annulus integral of ‖R_j‖² by ∑_{far ℓ} of annulus
  -- integral of ‖U_ℓ‖². Then block_annulus_leakage_symmetric bounds each (j,ℓ) pair.
  -- Step 2: ∑_j ∑_{far ℓ} = ∑_ℓ ∑_{far j} by Finset.sum_comm.
  -- Step 3: inner_sum_bound bounds the inner sum over far j.
  -- Step 4: fockNorm_decomposes collapses the outer sum.
  --
  -- We bound: LHS ≤ ∑_j ∑_{ℓ far from j} annulus_leakage(j,ℓ)
  -- ≤ ∑_j ∑_{ℓ ∈ Icc 1 Λ} [far] exp(1/4)*exp(-d²)*fockNormSqBlock(ℓ)
  -- = ∑_{ℓ ∈ Icc 1 Λ} fockNormSqBlock(ℓ) * (∑_{j far} exp(1/4)*exp(-d²))
  -- ≤ ∑_ℓ fockNormSqBlock(ℓ) * etaCoeff M J
  -- = etaCoeff M J * fockNormSq a
  calc ∑ j ∈ Finset.range J,
        2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
          (∫ t : AddCircle T,
            ‖remainderPoly a M j (↑r * (fourier 1 t : ℂ))‖ ^ 2
            ∂AddCircle.haarAddCircle)
      ≤ ∑ j ∈ Finset.range J,
        ∑ ℓ ∈ Finset.Icc 1 (maxBlockIndex D),
          if (j + M < ℓ ∨ ℓ + M < j) then
            2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
              (∫ t : AddCircle T,
                ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
                ∂AddCircle.haarAddCircle)
          else 0 := by
        apply Finset.sum_le_sum; intro j _
        exact remainder_annulus_le_far_blocks a (by omega : 1 ≤ M) j
    _ ≤ ∑ j ∈ Finset.range J,
        ∑ ℓ ∈ Finset.Icc 1 (maxBlockIndex D),
          if (j + M < ℓ ∨ ℓ + M < j) then
            Real.exp (1 / 4) *
              Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2) *
              fockNormSqBlock a ℓ
          else 0 := by
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro ℓ hℓ
        split_ifs with hfar
        · -- Apply block_annulus_leakage_symmetric
          have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
          exact block_annulus_leakage_symmetric a hℓ1 j
        · exact le_refl _
    _ = ∑ ℓ ∈ Finset.Icc 1 (maxBlockIndex D),
        ∑ j ∈ Finset.range J,
          if (j + M < ℓ ∨ ℓ + M < j) then
            Real.exp (1 / 4) *
              Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2) *
              fockNormSqBlock a ℓ
          else 0 := by rw [Finset.sum_comm]
    _ ≤ ∑ ℓ ∈ Finset.Icc 1 (maxBlockIndex D),
        fockNormSqBlock a ℓ * etaCoeff M J := by
        apply Finset.sum_le_sum; intro ℓ _
        -- Factor out fockNormSqBlock and bound inner sum
        -- ∑_j [far] exp(1/4)*exp(-d²)*fockNormSqBlock(ℓ)
        -- = fockNormSqBlock(ℓ) * (∑_j [far] exp(1/4)*exp(-d²))
        -- ≤ fockNormSqBlock(ℓ) * exp(1/4) * 2*∑_{m≥M} exp(-m²)
        -- = fockNormSqBlock(ℓ) * etaCoeff M J
        have hfnsq := fockNormSqBlock_nonneg a ℓ
        -- Extract constant factors
        conv_lhs =>
          arg 2; ext j
          rw [show (if (j + M < ℓ ∨ ℓ + M < j) then
              Real.exp (1 / 4) *
                Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2) *
                fockNormSqBlock a ℓ
            else 0) =
            (if (j + M < ℓ ∨ ℓ + M < j) then
              Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2)
            else 0) * (Real.exp (1 / 4) * fockNormSqBlock a ℓ)
            from by split_ifs <;> ring]
        rw [← Finset.sum_mul]
        -- Filter out the if condition
        rw [show ∑ j ∈ Finset.range J,
            (if (j + M < ℓ ∨ ℓ + M < j) then
              Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2)
            else 0) =
            ∑ j ∈ (Finset.range J).filter (fun j => j + M < ℓ ∨ ℓ + M < j),
              Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2)
          from by rw [Finset.sum_filter]]
        -- Apply inner_sum_bound
        have hℓJ : ℓ ≤ J :=
          le_trans (Finset.mem_Icc.mp ‹ℓ ∈ Finset.Icc 1 (maxBlockIndex D)›).2 hJbound
        have hinner := inner_sum_bound M J ℓ hM hℓJ
        -- Goal: (∑_{far j} exp(-d²)) * (exp(1/4) * fNSB) ≤ fNSB * etaCoeff M J
        -- etaCoeff M J = 2 * exp(1/4) * ∑ exp(-m²)
        -- Need: (∑ far) * exp(1/4) * fNSB ≤ fNSB * 2 * exp(1/4) * ∑ exp(-m²)
        -- i.e., ∑ far ≤ 2 * ∑ exp(-m²) (which is hinner)
        -- times exp(1/4) * fNSB ≥ 0
        calc (∑ j ∈ (Finset.range J).filter (fun j => j + M < ℓ ∨ ℓ + M < j),
              Real.exp (-(max (max ((j : ℤ) - ℓ - 1) ((ℓ : ℤ) - j - 1)) 0 : ℤ) ^ 2)) *
            (Real.exp (1 / 4) * fockNormSqBlock a ℓ)
          ≤ (2 * ∑ m ∈ Finset.Icc M J, Real.exp (-(m : ℝ) ^ 2)) *
            (Real.exp (1 / 4) * fockNormSqBlock a ℓ) :=
            mul_le_mul_of_nonneg_right hinner
              (mul_nonneg (le_of_lt (Real.exp_pos _)) hfnsq)
          _ = fockNormSqBlock a ℓ * etaCoeff M J := by unfold etaCoeff; ring
    _ = etaCoeff M J * fockNormSq a := by
        rw [fockNorm_decomposes]; simp only [fockNormSqBlock]
        rw [Finset.mul_sum]; congr 1; ext ℓ; ring

/-! ## Theorem 5.9: Explicit bound for η₅

`η₅ < 4 × 10⁻¹¹`

**Proof**: Bound `exp(1/4) < 13/10`, `exp(-25) < 14/10¹²`, `exp(-36) < 1/10¹⁴`.
Split the sum at `m = 5`, bound the tail by `95 · exp(-36)`.
-/

private lemma exp_quarter_lt : Real.exp (1 / 4 : ℝ) < 13 / 10 := by
  have h := Real.exp_bound'
    (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1:ℝ)/4 ≤ 1) (n := 5) (by norm_num)
  simp [Finset.sum_range_succ] at h; linarith

private lemma exp_neg_25_lt : Real.exp (-25 : ℝ) < 14 / 10 ^ 12 := by
  have h5 : (1484 : ℝ) / 10 ≤ Real.exp 5 := by
    have := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 5) 18
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    norm_num at this ⊢; linarith
  rw [show (-25 : ℝ) = (5 : ℕ) * (-5 : ℝ) from by norm_num,
      Real.exp_nat_mul, Real.exp_neg, inv_pow]
  calc (Real.exp 5 ^ 5)⁻¹
      ≤ ((1484 / 10 : ℝ) ^ 5)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h5 5)
    _ < 14 / 10 ^ 12 := by norm_num

private lemma exp_neg_36_lt : Real.exp (-36 : ℝ) < 1 / 10 ^ 14 := by
  have h6 : (403 : ℝ) ≤ Real.exp 6 := by
    have := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 6) 16
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    norm_num at this ⊢; linarith
  rw [show (-36 : ℝ) = (6 : ℕ) * (-6 : ℝ) from by norm_num,
      Real.exp_nat_mul, Real.exp_neg, inv_pow]
  calc (Real.exp 6 ^ 6)⁻¹
      ≤ ((403 : ℝ) ^ 6)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h6 6)
    _ < 1 / 10 ^ 14 := by norm_num

-- Numerical bound: etaCoeff uses exp which needs rational approximation
theorem eta_5_bound : etaCoeff 5 100 < 4 / (10 : ℝ) ^ 11 := by
  unfold etaCoeff
  -- Split sum: Σ_{m=5}^{100} exp(-m²) = exp(-25) + Σ_{m=6}^{100} exp(-m²)
  have hsplit : ∑ m ∈ (Finset.Icc 5 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) =
    Real.exp (-25) + ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) := by
    rw [show (Finset.Icc 5 100 : Finset ℕ) = insert 5 (Finset.Icc 6 100) from by
      ext m; simp [Finset.mem_Icc]; omega]
    rw [Finset.sum_insert (by decide)]
    congr 1; norm_num
  rw [hsplit]
  -- Bound the tail: Σ_{m=6}^{100} exp(-m²) ≤ 95 · exp(-36)
  have htail : ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) ≤
      95 * Real.exp (-36) := by
    calc ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2)
        ≤ ∑ _m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-36 : ℝ) :=
          Finset.sum_le_sum fun m hm => by
            apply Real.exp_le_exp.mpr
            simp only [Finset.mem_Icc] at hm
            have hm6 : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
            nlinarith [sq_nonneg ((m : ℝ) - 6)]
      _ = 95 * Real.exp (-36) := by simp [Finset.sum_const]
  -- Combine bounds
  have htail_bound : ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) <
      95 / 10 ^ 14 := by linarith [exp_neg_36_lt]
  have hsum_bound :
      Real.exp (-25) + ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) <
      14 / 10 ^ 12 + 95 / 10 ^ 14 := by linarith [exp_neg_25_lt]
  have hsum_pos :
      0 ≤ Real.exp (-25) +
        ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2) :=
    add_nonneg (le_of_lt (Real.exp_pos _))
      (Finset.sum_nonneg fun m _ => le_of_lt (Real.exp_pos _))
  -- 2 · exp(1/4) · sum < 2 · (13/10) · (14/10¹² + 95/10¹⁴) = 3887/10¹⁴ < 4/10¹¹
  have step1 : 2 * Real.exp (1 / 4) *
      (Real.exp (-25) + ∑ m ∈ (Finset.Icc 6 100 : Finset ℕ), Real.exp (-(m : ℝ) ^ 2)) <
      2 * (13 / 10) * (14 / 10 ^ 12 + 95 / 10 ^ 14) := by
    nlinarith [exp_quarter_lt, Real.exp_pos (1 / 4 : ℝ)]
  linarith [show (2 : ℝ) * (13 / 10) * (14 / 10 ^ 12 + 95 / 10 ^ 14) < 4 / 10 ^ 11
    from by norm_num]

end FockSPR
