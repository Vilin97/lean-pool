/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # HighFreqBandEstimate.lean
  High-frequency band estimate using Poincaré + rotational averaging.
  Scaffolding notes: HighFreqBandEstimate/high_freq_band.md

  Dependencies: Definitions, SafeSquare, LipschitzRho,
    RotationalAveraging, MissingMathlib/Poincare

  Public API:
  - `high_freq_band_estimate` (Theorem 4.1)
-/
import LeanPool.PhaseRetrieval.Constant.Internal.Definitions
import LeanPool.PhaseRetrieval.Constant.Internal.SafeSquare
import LeanPool.PhaseRetrieval.Constant.Internal.LipschitzRho
import LeanPool.PhaseRetrieval.Constant.Internal.RotationalAveraging
import LeanPool.PhaseRetrieval.Constant.Internal.MissingMathlib.Poincare
import Mathlib.Analysis.Real.Pi.Bounds

/-! # HighFreqBandEstimate -/


open MeasureTheory Complex Real Finset

noncomputable section

namespace FockSPR

/-! ## Slow factor and factorization -/

/-- The slow factor Q(t) = ∑ b(m) fourier(m)(t). -/
private def slowFactor {L : ℕ} (b : Fin L → ℂ) :
    AddCircle T → ℂ :=
  fun t => ∑ m : Fin L, b m * fourier (m.val : ℤ) t

/-- P(t) = fourier(N)(t) · Q(t). -/
private lemma P_eq_fourier_mul_Q {N L : ℕ}
    (b : Fin L → ℂ) (P : AddCircle T → ℂ)
    (hP : P = fun t =>
      ∑ m : Fin L,
        b m * fourier ((N + m.val : ℕ) : ℤ) t) :
    P = fun t =>
      fourier (N : ℤ) t * slowFactor b t := by
  ext t; rw [hP]
  simp only [slowFactor, Finset.mul_sum]
  congr 1; ext m
  rw [mul_comm (fourier (↑↑N) t), mul_assoc,
    ← fourier_add]
  congr 1; push_cast; ring_nf

-- to_mathlib: Mathlib.Analysis.Fourier.AddCircle
/-- Pointwise norm of a Fourier character is 1. -/
private lemma norm_fourier_apply (n : ℤ)
    (t : AddCircle T) : ‖fourier n t‖ = 1 := by rw [fourier_apply]; exact Circle.norm_coe _

/-- circleNormSq P = circleNormSq Q. -/
private lemma circleNormSq_P_eq_Q {N L : ℕ}
    (b : Fin L → ℂ) (P : AddCircle T → ℂ)
    (hP : P = fun t =>
      ∑ m : Fin L,
        b m * fourier ((N + m.val : ℕ) : ℤ) t) :
    circleNormSq P = circleNormSq (slowFactor b) := by
  unfold circleNormSq; congr 1; ext t
  have hPQ := P_eq_fourier_mul_Q b P hP
  simp only [hPQ, norm_mul, norm_fourier_apply,
    one_mul]

/-! ## Pointwise bounds -/

/-- ρ is nonnegative. -/
private lemma rho_nonneg' (w : ℂ) : 0 ≤ rho w :=
  abs_nonneg _

/-- For |α| = 1: ρ(αw)² ≥ (1/2)ρ(αz)² − ‖w−z‖².
    From `rho_pointwise_lower` + `nonneg_safe_square`. -/
private lemma rho_sq_lower (α w z : ℂ)
    (hα : ‖α‖ = 1) :
    (rho (α * w)) ^ 2 ≥
      (1 / 2) * (rho (α * z)) ^ 2 -
        ‖w - z‖ ^ 2 := by
  have h1 := rho_pointwise_lower (α * w) (α * z)
  have h2 : ‖α * w - α * z‖ = ‖w - z‖ := by rw [← mul_sub, norm_mul, hα, one_mul]
  exact nonneg_safe_square _ _ _
    (rho_nonneg' _) (rho_nonneg' _)
    (norm_nonneg _) (by linarith)

/-! ## Interval partition quantities -/

/-- Left endpoint of the k-th interval. -/
private def iLeft (N : ℕ) (k : ℕ) : ℝ :=
  T * k / N

/-- Average of Q on the k-th interval. -/
private def qAvg {L : ℕ} (b : Fin L → ℂ)
    (N : ℕ) (k : Fin N) : ℂ :=
  (↑N / (T : ℂ)) •
    ∫ t in iLeft N k.val..iLeft N (k.val + 1),
      slowFactor b (↑t : AddCircle T)

/-- Total approximation error δ. -/
private def totalDelta {L : ℕ} (b : Fin L → ℂ)
    (N : ℕ) : ℝ :=
  (1 / T) * ∑ k : Fin N,
    ∫ t in iLeft N k.val..iLeft N (k.val + 1),
      ‖slowFactor b (↑t : AddCircle T) -
        qAvg b N k‖ ^ 2

/-! ## Infrastructure: Haar-to-interval decomposition

The key identity relating Haar integrals on `AddCircle T` to
interval integrals on ℝ is:

  `∫ f ∂haarAddCircle = (1/T) ∑_{k=0}^{N-1} ∫_{I_k} f(↑t) dt`

This follows from:
- `AddCircle.integral_preimage`: `∫ₜ∈Ioc(0,T) f(↑t) dt = ∫ f ∂volume`
- `AddCircle.volume_eq_smul_haarAddCircle`: `volume = T • haarAddCircle`
- Additivity of interval integrals.
-/

-- to_mathlib: Mathlib.MeasureTheory.Integral.IntervalIntegral
/-- Haar integral equals (1/T) times the sum of interval integrals. -/
private lemma iLeft_zero (N : ℕ) : iLeft N 0 = 0 := by simp [iLeft]

private lemma iLeft_N (N : ℕ) (hN : 1 ≤ N) : iLeft N N = T := by
  unfold iLeft
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

private lemma haar_eq_sum_intervals {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {N : ℕ} (hN : 1 ≤ N) {f : AddCircle T → E}
    (hf : Continuous f) :
    ∫ t, f t ∂AddCircle.haarAddCircle =
      (1 / T) • ∑ k : Fin N,
        ∫ t in iLeft N k.val..iLeft N (k.val + 1),
          f (↑t : AddCircle T) := by
  -- Step 1: ∫ f ∂haar = T⁻¹ • ∫ f ∂volume
  rw [AddCircle.integral_haarAddCircle, show T⁻¹ = (1 / T) from by ring]
  congr 1
  -- Step 2: ∫ f ∂volume = ∫ t in 0..T, f ↑t (by AddCircle.intervalIntegral_preimage)
  rw [← AddCircle.intervalIntegral_preimage T 0 f]
  simp only [zero_add]
  -- Step 3: ∫ t in 0..T, f ↑t = ∑_k ∫ t in I_k, f ↑t
  set g : ℝ → E := fun t => f (↑t : AddCircle T)
  have hg_cont : Continuous g := hf.comp (AddCircle.continuous_mk' T)
  have h0 : iLeft N 0 = 0 := iLeft_zero N
  have hT : iLeft N N = T := iLeft_N N hN
  change ∫ t in (0:ℝ)..T, g t = ∑ k : Fin N, ∫ t in iLeft N k.val..iLeft N (k.val + 1), g t
  rw [← h0, ← hT]
  have hint : ∀ k < N, IntervalIntegrable g volume (iLeft N k) (iLeft N (k + 1)) :=
    fun k _ => hg_cont.intervalIntegrable _ _
  have := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [Finset.sum_range] at this
  exact this.symm

/-! ## Intermediate lemmas (4.1a–d) -/

/-- Bias-variance identity on each subinterval: for a function `g`
    with mean `c` on `[a,b]` (where `c = (1/(b-a)) ∫_a^b g`):
    `∫_a^b ‖g‖² = (b-a)·‖c‖² + ∫_a^b ‖g - c‖²`.
    Proof: ‖g(t)‖² = ‖c + (g(t)-c)‖² = ‖c‖² + 2Re⟪c, g(t)-c⟫ + ‖g(t)-c‖².
    The cross-term vanishes since ∫(g-c) = 0 by definition of c. -/
private lemma bias_variance_interval (a b : ℝ) (hab : a < b)
    (g : ℝ → ℂ) (c : ℂ)
    (hc : c = ((b - a)⁻¹ : ℝ) • ∫ t in a..b, g t)
    (hg : IntervalIntegrable g volume a b)
    (hg_cont : ContinuousOn g (Set.Icc a b)) :
    ∫ t in a..b, ‖g t‖ ^ 2 =
      (b - a) * ‖c‖ ^ 2 +
        ∫ t in a..b, ‖g t - c‖ ^ 2 := by
  have hgc : IntervalIntegrable (fun t => g t - c)
      volume a b := hg.sub intervalIntegrable_const
  -- Step 1: ∫(g-c) = 0
  have h_mean_zero : ∫ t in a..b, (g t - c) = 0 := by
    rw [intervalIntegral.integral_sub hg
      intervalIntegrable_const,
      intervalIntegral.integral_const, hc, sub_eq_zero]
    exact (smul_inv_smul₀
      (ne_of_gt (sub_pos.mpr hab)) _).symm
  -- Step 2: Cross-term vanishes
  have h_cross :
      ∫ t in a..b, @inner ℝ ℂ _ c (g t - c) = 0 := by
    have key : ∀ t, @inner ℝ ℂ _ c (g t - c) =
        (innerSL ℝ c) (g t - c) := by intro t; simp [innerSL_apply_apply]
    simp_rw [key]
    rw [ContinuousLinearMap.intervalIntegral_comp_comm
      (innerSL ℝ c) hgc, h_mean_zero,
      map_zero]
  -- Step 3: Pointwise identity
  have h_pw : ∀ t, ‖g t‖ ^ 2 - ‖g t - c‖ ^ 2 =
      2 * @inner ℝ ℂ _ c (g t - c) + ‖c‖ ^ 2 := by
    intro t; have := norm_add_sq_real c (g t - c)
    simp only [add_sub_cancel] at this; linarith
  -- Step 4: Integrate and combine
  have h1 : ∫ t in a..b,
      (‖g t‖ ^ 2 - ‖g t - c‖ ^ 2) =
    ∫ t in a..b,
      (2 * @inner ℝ ℂ _ c (g t - c) + ‖c‖ ^ 2) := by congr 1; ext t; exact h_pw t
  -- Integrability from continuity on compact interval
  have hgc_cont : ContinuousOn (fun t => g t - c) (Set.Icc a b) :=
    hg_cont.sub continuousOn_const
  have hi_g2 : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume a b :=
    (hg_cont.norm.pow 2).intervalIntegrable_of_Icc (le_of_lt hab)
  have hi_gc2 : IntervalIntegrable (fun t => ‖g t - c‖ ^ 2) volume a b :=
    (hgc_cont.norm.pow 2).intervalIntegrable_of_Icc (le_of_lt hab)
  -- Step 5: Split LHS of h1
  have h_split : ∫ t in a..b, (‖g t‖ ^ 2 - ‖g t - c‖ ^ 2) =
      (∫ t in a..b, ‖g t‖ ^ 2) - ∫ t in a..b, ‖g t - c‖ ^ 2 :=
    intervalIntegral.integral_sub hi_g2 hi_gc2
  -- Step 6: Evaluate RHS of h1
  have hi_cross : IntervalIntegrable
      (fun t => @inner ℝ ℂ _ c (g t - c)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hab)
    exact (continuous_const.inner continuous_id).comp_continuousOn hgc_cont
  have hi_2cross : IntervalIntegrable
      (fun t => 2 * @inner ℝ ℂ _ c (g t - c)) volume a b :=
    hi_cross.const_mul 2
  have h_rhs : ∫ t in a..b,
      (2 * @inner ℝ ℂ _ c (g t - c) + ‖c‖ ^ 2) =
    2 * (∫ t in a..b, @inner ℝ ℂ _ c (g t - c)) +
      (b - a) * ‖c‖ ^ 2 := by
    rw [intervalIntegral.integral_add hi_2cross
      intervalIntegrable_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
  -- Combine
  linarith [h1, h_split, h_rhs, h_cross]

/-- 4.1b: Parseval partition identity.
    On each I_k, ∫|Q|² = |q_k|²·(T/N)/T + ∫|Q−q_k|²
    since q_k is the mean and the cross-term vanishes.

    Proof: Apply the Haar-to-interval decomposition to express
    circleNormSq(Q) = (1/T) ∑_k ∫_{I_k} ‖Q‖² dt.
    On each I_k, apply bias_variance_interval with c = q_k.
    The variance terms sum to totalDelta, and the bias terms
    give (1/N) ∑_k ‖q_k‖². -/
-- The interval length is T/N.
private lemma iLeft_diff (N : ℕ) (k : ℕ) :
    iLeft N (k + 1) - iLeft N k = T / N := by simp [iLeft]; ring

-- Interval endpoints are monotone.
private lemma iLeft_lt_iLeft (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    iLeft N k < iLeft N (k + 1) := by
  have hN_pos : (0 : ℝ) < (↑N : ℝ) := Nat.cast_pos.mpr (by omega)
  unfold iLeft
  apply div_lt_div_of_pos_right _ hN_pos
  have : (↑k : ℝ) < (↑(k + 1) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le le_rfl
  exact mul_lt_mul_of_pos_left this T_pos

-- rho is continuous.
private lemma rho_continuous : Continuous (rho : ℂ → ℝ) :=
  continuous_abs.comp
    (continuous_norm.comp (continuous_const.add continuous_id) |>.sub continuous_const)

-- slowFactor is continuous (finite sum of continuous terms).
private lemma slowFactor_continuous {L : ℕ} (b : Fin L → ℂ) :
    Continuous (slowFactor b) := by
  apply continuous_finsetSum
  intro m _
  exact continuous_const.mul (fourier (m.val : ℤ)).continuous

private lemma parseval_partition {N L : ℕ}
    (hN : 1 ≤ N) (b : Fin L → ℂ) :
    circleNormSq (slowFactor b) =
      (1 / ↑N) *
        ∑ k : Fin N, ‖qAvg b N k‖ ^ 2 +
        totalDelta b N := by
  set Q := slowFactor b
  have hQ_cont := slowFactor_continuous b
  -- Step 1: circleNormSq(Q) = (1/T) ∑_k ∫_{I_k} ‖Q(↑t)‖² dt
  have hQ2_cont : Continuous (fun t : AddCircle T => ‖Q t‖ ^ 2) :=
    (hQ_cont.norm.pow 2)
  have h_haar := haar_eq_sum_intervals hN hQ2_cont
  unfold circleNormSq
  rw [h_haar]
  -- Now goal: (1/T) • ∑_k ∫_{I_k} ‖Q(↑t)‖² = (1/N) ∑‖q_k‖² + totalDelta
  -- Step 2: On each I_k, apply bias_variance_interval
  have hT_pos : (0 : ℝ) < T := T_pos
  have hN_pos : (0 : ℝ) < (↑N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hTN_pos : (0 : ℝ) < T / ↑N := div_pos hT_pos hN_pos
  -- Each interval has length T/N
  -- qAvg b N k = (N/T : ℂ) • ∫_{I_k} Q = ((T/N)⁻¹ : ℝ) • ∫_{I_k} Q
  -- so it is the mean value for bias_variance_interval
  have hQ_comp_cont : Continuous (fun t : ℝ => Q (↑t : AddCircle T)) :=
    hQ_cont.comp (AddCircle.continuous_mk' T)
  have hQ_intble : ∀ k : Fin N,
      IntervalIntegrable (fun t => Q (↑t : AddCircle T)) volume
        (iLeft N k.val) (iLeft N (k.val + 1)) :=
    fun k => hQ_comp_cont.intervalIntegrable _ _
  -- The mean condition: qAvg matches the bias_variance format
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have h_qavg_mean : ∀ k : Fin N,
      qAvg b N k = ((iLeft N (k.val + 1) - iLeft N k.val)⁻¹ : ℝ) •
        ∫ t in iLeft N k.val..iLeft N (k.val + 1), Q (↑t : AddCircle T) := by
    intro k
    simp only [qAvg, iLeft_diff]
    -- Need: (↑N / (T : ℂ)) • I = ((T/N)⁻¹ : ℝ) • I
    -- (T/N)⁻¹ = N/T as reals, and (↑N / T : ℂ) = ↑(N/T : ℝ)
    rw [show (T / (↑N : ℝ))⁻¹ = (↑N : ℝ) / T from by field_simp]
    rw [show ((↑N : ℝ) / T) = ((↑N : ℝ) * T⁻¹) from by ring]
    rw [show (↑N / (T : ℂ)) = (((↑N : ℝ) * T⁻¹ : ℝ) : ℂ) from by
      push_cast; field_simp]
    exact (Complex.coe_smul _ _).symm
  -- Bias-variance on each interval
  have h_bv : ∀ k : Fin N,
      ∫ t in iLeft N k.val..iLeft N (k.val + 1), ‖Q (↑t : AddCircle T)‖ ^ 2 =
      (T / ↑N) * ‖qAvg b N k‖ ^ 2 +
        ∫ t in iLeft N k.val..iLeft N (k.val + 1),
          ‖Q (↑t : AddCircle T) - qAvg b N k‖ ^ 2 := by
    intro k
    have := bias_variance_interval (iLeft N k.val) (iLeft N (k.val + 1))
      (iLeft_lt_iLeft N hN k.val)
      (fun t => Q (↑t : AddCircle T)) (qAvg b N k)
      (h_qavg_mean k) (hQ_intble k) hQ_comp_cont.continuousOn
    rwa [iLeft_diff] at this
  -- Sum the bias-variance identities
  have h_sum : ∑ k : Fin N, ∫ t in iLeft N k.val..iLeft N (k.val + 1),
      ‖Q (↑t : AddCircle T)‖ ^ 2 =
    (T / ↑N) * ∑ k : Fin N, ‖qAvg b N k‖ ^ 2 +
      ∑ k : Fin N, ∫ t in iLeft N k.val..iLeft N (k.val + 1),
        ‖Q (↑t : AddCircle T) - qAvg b N k‖ ^ 2 := by
    have : ∀ k ∈ Finset.univ, ∫ t in iLeft N k.val..iLeft N (k.val + 1),
        ‖Q (↑t : AddCircle T)‖ ^ 2 =
      T / ↑N * ‖qAvg b N k‖ ^ 2 +
        ∫ t in iLeft N k.val..iLeft N (k.val + 1),
          ‖Q (↑t : AddCircle T) - qAvg b N k‖ ^ 2 :=
      fun k _ => h_bv k
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h_sum]
  -- Now: (1/T) • ((T/N) * ∑‖q_k‖² + ∑∫‖Q-q_k‖²)
  --    = (1/T)(T/N) * ∑‖q_k‖² + (1/T) * ∑∫‖Q-q_k‖²
  --    = (1/N) * ∑‖q_k‖² + totalDelta
  simp only [smul_eq_mul]
  unfold totalDelta Q
  have hT_ne' : T ≠ 0 := ne_of_gt hT_pos
  field_simp

/-! ## Parseval identity for finite Fourier sums indexed by Fin L -/

private lemma parseval_fin_fourier {L : ℕ} (c : Fin L → ℂ) :
    circleNormSq (fun t : AddCircle T =>
      ∑ m : Fin L, c m * fourier (m.val : ℤ) t) =
    ∑ m : Fin L, ‖c m‖ ^ 2 := by
  let E := Finset.range L
  let b' : ℕ → ℂ := fun n =>
    if h : n < L then c ⟨n, h⟩ else 0
  -- Convert Fin L sum to range L sum
  have h_func_eq :
      (fun t : AddCircle T =>
        ∑ m : Fin L, c m * fourier (↑↑m : ℤ) t) =
      fun t => ∑ n ∈ E, b' n * fourier (↑n : ℤ) t := by
    ext t; simp only [E]; rw [@sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp [b', Finset.mem_range.mp hn]
  rw [h_func_eq]
  -- Set up L² machinery
  let Pcont : C(AddCircle T, ℂ) :=
    ∑ n ∈ E, b' n • fourier (n : ℤ)
  let PLp := (ContinuousMap.toLp
    (α := AddCircle T) 2 AddCircle.haarAddCircle ℂ) Pcont
  let E' :=
    E.map ⟨(Nat.cast : ℕ → ℤ), Nat.cast_injective⟩
  let d : ℤ → ℂ := fun k => b' (Int.toNat k)
  have hPLp : PLp = ∑ k ∈ E', d k • fourierLp 2 k := by
    simp only [PLp, Pcont, E', d, fourierLp,
      map_sum, map_smul]
    rw [Finset.sum_map]; simp
  have hinner_orth :
      @inner ℂ _ _ PLp PLp =
        Complex.ofReal (∑ n ∈ E, ‖b' n‖ ^ 2) := by
    rw [hPLp, orthonormal_fourier.inner_sum d d E',
      show E' = E.map ⟨(Nat.cast : ℕ → ℤ),
        Nat.cast_injective⟩ from rfl,
      Finset.sum_map, Complex.ofReal_sum]
    congr 1; ext n
    simp only [Function.Embedding.coeFn_mk, d,
      Int.toNat_natCast]
    rw [mul_comm, mul_conj]; congr 1
    exact (Complex.sq_norm (b' n)).symm
  have hcombine :=
    (L2.inner_def (𝕜 := ℂ) PLp PLp).symm.trans hinner_orth
  have hae := ContinuousMap.coeFn_toLp
    (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) (p := 2) Pcont
  have hPcont_eq :
      ∀ t : AddCircle T, (Pcont : AddCircle T → ℂ) t =
        ∑ n ∈ E, b' n * (fourier (n : ℤ)) t := by
    intro t
    simp [Pcont, ContinuousMap.coe_sum,
      ContinuousMap.coe_smul, smul_eq_mul]
  -- Convert range L sums back to Fin L
  have h_sum_eq :
      ∑ n ∈ E, ‖b' n‖ ^ 2 = ∑ m : Fin L, ‖c m‖ ^ 2 := by
    simp only [E]; rw [@sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp [b', Finset.mem_range.mp hn]
  calc circleNormSq
        (fun t => ∑ n ∈ E, b' n * (fourier (↑n : ℤ)) t)
      = ∫ t : AddCircle T,
          ‖(↑↑PLp : AddCircle T → ℂ) t‖ ^ 2
            ∂AddCircle.haarAddCircle := by
        unfold circleNormSq; symm; apply integral_congr_ae
        filter_upwards [hae] with t ht
        rw [show (↑↑PLp : AddCircle T → ℂ) t =
          Pcont t from ht, hPcont_eq t]
    _ = (∫ t : AddCircle T,
          @inner ℂ ℂ _
            ((↑↑PLp : AddCircle T → ℂ) t)
            ((↑↑PLp : AddCircle T → ℂ) t)
            ∂AddCircle.haarAddCircle).re := by
        have hint :=
          L2.integrable_inner (𝕜 := ℂ) PLp PLp
        symm
        calc _ = Complex.reCLM (∫ t,
              @inner ℂ ℂ _
                ((↑↑PLp : AddCircle T → ℂ) t)
                ((↑↑PLp : AddCircle T → ℂ) t)
                ∂AddCircle.haarAddCircle) := rfl
          _ = ∫ t, Complex.reCLM
              (@inner ℂ ℂ _
                ((↑↑PLp : AddCircle T → ℂ) t)
                ((↑↑PLp : AddCircle T → ℂ) t))
              ∂AddCircle.haarAddCircle :=
            (ContinuousLinearMap.integral_comp_comm
              _ hint).symm
          _ = _ := by
            congr 1; ext t
            exact @inner_self_eq_norm_sq ℂ ℂ _ _ _
              ((↑↑PLp : AddCircle T → ℂ) t)
    _ = ∑ m : Fin L, ‖c m‖ ^ 2 := by
        rw [show (∫ t : AddCircle T,
            @inner ℂ ℂ _
              ((↑↑PLp : AddCircle T → ℂ) t)
              ((↑↑PLp : AddCircle T → ℂ) t)
              ∂AddCircle.haarAddCircle) =
            Complex.ofReal (∑ n ∈ E, ‖b' n‖ ^ 2)
          from hcombine, Complex.ofReal_re, h_sum_eq]

/-- Derivative L² norm bounded by (L-1)² times function
    L² norm (Parseval). -/
private lemma deriv_norm_le_circleNormSq {N L : ℕ} (hN : 1 ≤ N)
    (b : Fin L → ℂ) :
    (1 / T) * ∑ k : Fin N,
      ∫ t in iLeft N k.val..iLeft N (k.val + 1),
        ‖(fun t => ∑ m : Fin L,
          b m * ((2 * Real.pi * Complex.I * ↑(m.val : ℤ) / (T : ℂ)) *
          fourier (m.val : ℤ) (↑t : AddCircle T))) t‖ ^ 2 ≤
    (↑L - 1) ^ 2 * circleNormSq (slowFactor b) := by
  set Q := slowFactor b
  set Q' : ℝ → ℂ := fun t => ∑ m : Fin L,
    b m * ((2 * Real.pi * Complex.I * ↑(m.val : ℤ) / (T : ℂ)) *
    fourier (m.val : ℤ) (↑t : AddCircle T))
  -- Define Q'_circle on AddCircle T
  set Q'_circle : AddCircle T → ℂ := fun t => ∑ m : Fin L,
    b m * ((2 * Real.pi * Complex.I * ↑(m.val : ℤ) / (T : ℂ)) *
    fourier (m.val : ℤ) t)
  have hQ'_eq : ∀ t : ℝ, Q' t = Q'_circle (↑t : AddCircle T) := fun _ => rfl
  have hQ'_cont : Continuous Q'_circle := by
    apply continuous_finsetSum; intro m _
    exact continuous_const.mul (continuous_const.mul (fourier (m.val : ℤ)).continuous)
  have h_haar := haar_eq_sum_intervals hN (hQ'_cont.norm.pow 2)
  have h_lhs : (1 / T) * ∑ k : Fin N,
      ∫ t in iLeft N k.val..iLeft N (k.val + 1), ‖Q' t‖ ^ 2 =
      circleNormSq Q'_circle := by unfold circleNormSq; rw [h_haar, smul_eq_mul]
  rw [h_lhs]
  -- Rewrite Q'_circle as a Fourier sum with
  -- coefficients c(m) = b(m) * (2πim/T)
  have h_Q'_rewrite :
      Q'_circle = fun t => ∑ m : Fin L,
        (b m * (2 * Real.pi * Complex.I *
          ↑(m.val : ℤ) / (T : ℂ))) *
        fourier (m.val : ℤ) t := by
    ext t; apply Finset.sum_congr rfl; intro m _
    ring
  have h_parseval_Q' : circleNormSq Q'_circle =
      ∑ m : Fin L,
        ‖b m * (2 * Real.pi * Complex.I *
          ↑(m.val : ℤ) / (T : ℂ))‖ ^ 2 := by rw [h_Q'_rewrite]; exact parseval_fin_fourier _
  have h_parseval_Q :
      circleNormSq Q = ∑ m : Fin L, ‖b m‖ ^ 2 := by
    change circleNormSq
      (fun t => ∑ m : Fin L, b m * fourier (↑↑m : ℤ) t) = _
    exact parseval_fin_fourier b
  have h_coeff_norm : ∀ m : Fin L,
      ‖b m * (2 * Real.pi * Complex.I *
        ↑(m.val : ℤ) / (T : ℂ))‖ ^ 2 =
      (m.val : ℝ) ^ 2 * ‖b m‖ ^ 2 := by
    intro m
    have hsimpl :
        (2 * ↑π * Complex.I * ↑(m.val : ℤ) / (T : ℂ)) =
          Complex.I * (m.val : ℂ) := by simp only [T]; push_cast; field_simp
    rw [hsimpl, norm_mul, norm_mul, Complex.norm_I,
      one_mul, Complex.norm_natCast]; ring
  simp_rw [h_parseval_Q', h_coeff_norm, h_parseval_Q]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro m _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hm : (m.val : ℝ) ≤ ↑L - 1 := by
    have := m.isLt; exact_mod_cast (show (m.val : ℤ) ≤ (L : ℤ) - 1 by omega)
  exact sq_le_sq' (by linarith [Nat.cast_nonneg (α := ℝ) m.val]) hm


/-- Interval integral shift: ∫_a^{a+h} g = ∫_0^h g(·+a). -/
private lemma integral_shift {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (a h : ℝ) :
    ∫ t in a..a + h, g t =
      ∫ x in (0 : ℝ)..h, g (x + a) := by
  have key := (intervalIntegral.integral_comp_add_right
    g a (a := (0 : ℝ)) (b := h)).symm
  simp only [zero_add] at key
  rwa [add_comm h a] at key

/-- Derivative of the shifted slow factor `x ↦ slowFactor b (↑(x + a))`.
Isolated as its own lemma so the large `HasDerivAt.fun_sum` term elaborates
without the surrounding `set`/`let` bindings inflating the definitional checks. -/
private lemma hasDerivAt_slowFactor_shift {L : ℕ} (b : Fin L → ℂ) (a x : ℝ) :
    HasDerivAt (fun x : ℝ => slowFactor b (↑(x + a) : AddCircle T))
      (∑ m : Fin L,
        b m * (2 * Real.pi * Complex.I * ↑(m.val : ℤ) / (T : ℂ) *
          fourier (m.val : ℤ) (↑(x + a) : AddCircle T))) x := by
  have hterm : ∀ m : Fin L,
      HasDerivAt (fun y : ℝ => b m * fourier (m.val : ℤ) (↑(y + a) : AddCircle T))
        (b m * (2 * Real.pi * Complex.I * ↑(m.val : ℤ) / (T : ℂ) *
          fourier (m.val : ℤ) (↑(x + a) : AddCircle T))) x := by
    intro m
    have hd :=
      HasDerivAt.scomp
        (x := x)
        (h := fun y : ℝ => y + a)
        (g₁ := fun y : ℝ => (fourier (m.val : ℤ) (↑y : AddCircle T) : ℂ))
        (hasDerivAt_fourier T (m.val : ℤ) (x + a))
        (hasDerivAt_id x |>.add (hasDerivAt_const x a))
    simp only [add_zero, one_smul] at hd
    exact hd.const_mul _
  simpa only [slowFactor] using
    HasDerivAt.fun_sum (u := Finset.univ) fun m _ => hterm m

/-- Poincaré on each subinterval: shifted to [0, h] and
    apply poincare_interval. -/
private lemma poincare_per_interval {N L : ℕ} (hN : 1 ≤ N)
    (b : Fin L → ℂ) (k : Fin N) :
    ∫ t in iLeft N k.val..iLeft N (k.val + 1),
      ‖slowFactor b (↑t : AddCircle T) - qAvg b N k‖ ^ 2 ≤
    (T / ↑N) ^ 2 * ∫ t in iLeft N k.val..iLeft N (k.val + 1),
      ‖∑ m : Fin L,
          b m * ((2 * Real.pi * Complex.I *
            ↑(m.val : ℤ) / (T : ℂ)) *
            fourier (m.val : ℤ) (↑t : AddCircle T))‖ ^ 2 := by
  set Q := slowFactor b
  set h := T / ↑N
  set Q' : ℝ → ℂ := fun t => ∑ m : Fin L,
    b m * ((2 * Real.pi * Complex.I *
      ↑(m.val : ℤ) / (T : ℂ)) *
      fourier (m.val : ℤ) (↑t : AddCircle T))
  have hT_pos : (0 : ℝ) < T := T_pos
  have hN_pos : (0 : ℝ) < (↑N : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hh_pos : 0 < h := div_pos hT_pos hN_pos
  set a := iLeft N k.val
  set f : ℝ → ℂ := fun x => Q (↑(x + a) : AddCircle T)
  set f' : ℝ → ℂ := fun x => Q' (x + a)
  have h_shift_lhs :
      ∫ t in a..a + h,
        ‖Q (↑t : AddCircle T) - qAvg b N k‖ ^ 2 =
      ∫ x in (0 : ℝ)..h,
        ‖f x - qAvg b N k‖ ^ 2 := by
    simp only [f]
    exact integral_shift (fun t =>
      ‖Q (↑t : AddCircle T) - qAvg b N k‖ ^ 2) a h
  have h_shift_rhs :
      ∫ t in a..a + h, ‖Q' t‖ ^ 2 =
      ∫ x in (0 : ℝ)..h, ‖f' x‖ ^ 2 := by
    simp only [f']
    exact integral_shift (fun t => ‖Q' t‖ ^ 2) a h
  have h_ak : iLeft N (k.val + 1) = a + h := by simp only [a, h]; linarith [iLeft_diff N k.val]
  rw [h_ak, h_shift_lhs, h_shift_rhs]
  have hf_deriv :
      ∀ x ∈ Set.Icc 0 h,
        HasDerivAt f (f' x) x := by
    intro x _
    simpa only [f, f', Q, Q'] using hasDerivAt_slowFactor_shift b a x
  have hf_cont : ContinuousOn f (Set.Icc 0 h) :=
    ((slowFactor_continuous b).comp
      (AddCircle.continuous_mk' T |>.comp
        (continuous_id.add
          continuous_const))).continuousOn
  have hf'_cont :
      ContinuousOn f' (Set.Icc 0 h) := by
    apply Continuous.continuousOn
    show Continuous f'
    have hcont :
        Continuous (fun x : ℝ => ∑ m : Fin L,
          b m * ((2 * Real.pi * Complex.I * ↑(m.val : ℤ) / (T : ℂ)) *
            fourier (m.val : ℤ) (↑(x + a) : AddCircle T))) :=
      continuous_finsetSum Finset.univ fun m _ =>
        continuous_const.mul
          (continuous_const.mul
            ((fourier (m.val : ℤ)).continuous.comp
              ((AddCircle.continuous_mk' T).comp
                (continuous_id.add continuous_const))))
    exact hcont
  have h_mean_smul :
      (1 / h) • ∫ x in (0 : ℝ)..h, f x =
        qAvg b N k := by
    simp only [f]
    rw [← integral_shift
      (fun x => Q (↑x : AddCircle T)) a h]
    rw [show a + h = iLeft N (k.val + 1)
      from h_ak.symm]
    simp only [qAvg]
    rw [show (1 : ℝ) / h = ↑N / T from by simp [h]]
    rw [show (↑N / T : ℝ) •
        ∫ t in a..iLeft N (k.val + 1),
          Q (↑t : AddCircle T) =
      (↑N / (T : ℂ)) •
        ∫ t in a..iLeft N (k.val + 1),
          Q (↑t : AddCircle T) from by
      rw [show (↑N / (T : ℂ)) = ((↑N / T : ℝ) : ℂ)
        from by push_cast; field_simp]
      exact (Complex.coe_smul _ _).symm]
  have h_mean_inv :
      h⁻¹ • ∫ x in (0 : ℝ)..h, f x =
        qAvg b N k := by simpa only [one_div] using h_mean_smul
  have hp := FockSPR.MissingMathlib.poincare_interval
    hh_pos hf_deriv hf_cont hf'_cont
  simp only [one_div] at hp
  rwa [h_mean_inv] at hp

/-- 4.1a: Poincaré bound with (L−1)² derivative bound. -/
private lemma poincare_bound {N L : ℕ} (hN : 1 ≤ N)
    (_hL : 1 ≤ L) (b : Fin L → ℂ) :
    totalDelta b N ≤
      (4 * Real.pi ^ 2 * (↑L - 1) ^ 2 /
        ↑N ^ 2) *
        circleNormSq (slowFactor b) := by
  have hT_pos : (0 : ℝ) < T := T_pos
  have hN_pos : (0 : ℝ) < (↑N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  set Q := slowFactor b
  set h := T / ↑N with hh_def
  set Q' : ℝ → ℂ := fun t => ∑ m : Fin L,
    b m * ((2 * Real.pi * Complex.I * ↑(m.val : ℤ) / (T : ℂ)) *
    fourier (m.val : ℤ) (↑t : AddCircle T))
  have h_per_k : ∀ k : Fin N,
      ∫ t in iLeft N k.val..iLeft N (k.val + 1),
        ‖Q (↑t : AddCircle T) - qAvg b N k‖ ^ 2 ≤
      h ^ 2 * ∫ t in iLeft N k.val..iLeft N (k.val + 1), ‖Q' t‖ ^ 2 :=
    fun k => poincare_per_interval hN b k
  have h_deriv_bound : (1 / T) * ∑ k : Fin N,
      ∫ t in iLeft N k.val..iLeft N (k.val + 1), ‖Q' t‖ ^ 2 ≤
    (↑L - 1) ^ 2 * circleNormSq Q :=
    deriv_norm_le_circleNormSq hN b
  -- Step 4: Combine
  unfold totalDelta
  have hC_nn : 0 ≤ circleNormSq Q := by
    unfold circleNormSq
    apply integral_nonneg
    intro
    positivity
  -- totalDelta = (1/T) ∑ ∫ ‖Q-q_k‖² ≤ (1/T) ∑ h² ∫ ‖Q'‖²
  --           = h² · (1/T) ∑ ∫ ‖Q'‖² ≤ h² · (L-1)² · circleNormSq(Q)
  --           = (T²/N²)(L-1)² circleNormSq(Q) = (4π²(L-1)²/N²) circleNormSq(Q)
  calc (1 / T) * ∑ k : Fin N, ∫ t in iLeft N k.val..iLeft N (k.val + 1),
        ‖Q (↑t : AddCircle T) - qAvg b N k‖ ^ 2
      ≤ (1 / T) * ∑ k : Fin N, (h ^ 2 * ∫ t in iLeft N k.val..iLeft N (k.val + 1),
          ‖Q' t‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun k _ => h_per_k k)
    _ = h ^ 2 * ((1 / T) * ∑ k : Fin N,
          ∫ t in iLeft N k.val..iLeft N (k.val + 1), ‖Q' t‖ ^ 2) := by
        rw [← Finset.mul_sum, mul_left_comm]
    _ ≤ h ^ 2 * ((↑L - 1) ^ 2 * circleNormSq Q) :=
        mul_le_mul_of_nonneg_left h_deriv_bound (sq_nonneg _)
    _ = (4 * Real.pi ^ 2 * (↑L - 1) ^ 2 / ↑N ^ 2) * circleNormSq Q := by
        simp only [h, T]; field_simp; ring


/-- 4.1c: Frozen rotation bound.
    Uses `rotational_averaging_bound` after a change of
    variables showing fourier(N) traverses one full period
    on each subinterval.

    Proof: On I_k = [2πk/N, 2π(k+1)/N], substitute s = N(t - 2πk/N).
    Then fourier(N)(↑t) = e^{iNt} = e^{i(s+2πk)} = e^{is} = fourier(1)(↑s)
    and dt = ds/N. So:
      ∫_{I_k} ρ(fourier(N)(t)·q_k)² dt = (1/N) ∫_0^{2π} ρ(fourier(1)(s)·q_k)² ds
      = (T/N) ∫ ρ(fourier(1)·q_k)² d(haar)
    Write q_k = r·α with r = ‖q_k‖. By Haar-invariance under rotation:
      = (T/N) ∫ ρ(r·fourier(1))² d(haar)
      ≥ (T/N) · r²/8  (by rotational_averaging_bound)
    Therefore (1/T) · ∫_{I_k} ≥ r²/(8N) = ‖q_k‖²/(8N). -/
-- Key fact: On interval I_k, the Fourier character fourier(N) completes one full period.
-- After change of variables, the integral over I_k of g(fourier(N)(t))
-- equals (1/N) * ∫_0^T g(fourier(1)(s)) ds = (T/N) * ∫ g(fourier(1)) d(haar).
-- Combined with rotation invariance of Haar measure (for the phase of q_k),
-- we get the frozen rotation bound using rotational_averaging_bound.
private lemma frozen_rotation {N L : ℕ} (hN : 1 ≤ N)
    (b : Fin L → ℂ) (k : Fin N) :
    (1 / T) *
      ∫ t in iLeft N k.val..iLeft N (k.val + 1),
        (rho (fourier (N : ℤ)
          (↑t : AddCircle T) *
            qAvg b N k)) ^ 2 ≥
      ‖qAvg b N k‖ ^ 2 / (8 * ↑N) := by
  set q := qAvg b N k
  have hT_pos : (0 : ℝ) < T := T_pos
  have hN_pos : (0 : ℝ) < (↑N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  -- Step A: Show ∫_{I_k} ρ(fourier(N)(t)·q)² dt = N⁻¹ · T · ∫ ρ(fourier(1)·q)² d(haar)
  -- via change of variables + periodicity + intervalIntegral_preimage.
  -- A1: fourier(N)(↑(s/N)) = fourier(1)(↑s) via explicit formula
  have fourier_rescale : ∀ s : ℝ,
      fourier (N : ℤ) (↑(s / ↑N) : AddCircle T) =
      fourier (1 : ℤ) (↑s : AddCircle T) := by
    intro s; simp only [fourier_coe_apply]
    congr 1
    have : (↑N : ℂ) ≠ 0 := by exact_mod_cast hN_ne
    have : (↑T : ℂ) ≠ 0 := by exact_mod_cast hT_ne
    push_cast; field_simp
  -- A2: Setup functions
  set g : ℝ → ℝ := fun t => (rho (fourier (N : ℤ) (↑t : AddCircle T) * q)) ^ 2
  -- A3: Change of variables + periodicity + preimage to get Haar integral
  have h_eq_haar_int : ∫ t in iLeft N k.val..iLeft N (k.val + 1), g t =
      (↑N : ℝ)⁻¹ * (T *
        ∫ t : AddCircle T,
          (rho (fourier (1 : ℤ) t * q)) ^ 2
            ∂AddCircle.haarAddCircle) := by
    -- integral_comp_mul_left: ∫ x in a..b, f(c*x) = c⁻¹ • ∫ x in c*a..c*b, f(x)
    have key := intervalIntegral.integral_comp_mul_left
      (fun s => g (s / ↑N)) hN_ne (a := iLeft N k.val) (b := iLeft N (k.val + 1))
    have h_simp : (fun x => g ((↑N : ℝ) * x / ↑N)) = g := by
      ext x; show g (↑N * x / ↑N) = g x; congr 1; field_simp
    rw [h_simp] at key
    have h_el : (↑N : ℝ) * iLeft N k.val = T * ↑k.val := by unfold iLeft; field_simp
    have h_er : (↑N : ℝ) * iLeft N (k.val + 1) = T * (↑k.val + 1) := by
      unfold iLeft; push_cast; field_simp
    rw [h_el, h_er] at key; rw [key, smul_eq_mul]; congr 1
    -- Replace g(s/N) by ρ(fourier(1)·q)²
    have h_congr : ∀ s ∈ Set.uIcc (T * ↑k.val) (T * (↑k.val + 1)),
        g (s / ↑N) = (rho (fourier (1 : ℤ) (↑s : AddCircle T) * q)) ^ 2 := by
      intro s _;
      change (rho (fourier (N : ℤ) (↑(s / ↑N) : AddCircle T) * q)) ^ 2 = _
      rw [fourier_rescale]
    rw [intervalIntegral.integral_congr h_congr]
    -- Periodicity: ∫_{T·k}^{T·(k+1)} = ∫_0^{0+T}
    set g₁ : ℝ → ℝ := fun s => (rho (fourier (1 : ℤ) (↑s : AddCircle T) * q)) ^ 2
    have hg₁_periodic : Function.Periodic g₁ T := by
      intro s; change (rho (fourier (1 : ℤ) (↑(s + T) : AddCircle T) * q)) ^ 2 =
        (rho (fourier (1 : ℤ) (↑s : AddCircle T) * q)) ^ 2
      simp only [QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.mem_zmultiples T)]
    rw [show T * (↑k.val + 1) = T * ↑k.val + T from by ring]
    rw [hg₁_periodic.intervalIntegral_add_eq (T * ↑k.val) 0]
    -- ∫_0^{0+T} g₁ = ∫ g₁ d(volume) = T * ∫ g₁ d(haar)
    -- g₁ s = (fun t => (rho (fourier 1 t * q))^2) (↑s)
    -- Use intervalIntegral_preimage and integral_haarAddCircle
    have h_preimage := AddCircle.intervalIntegral_preimage T 0
      (fun t : AddCircle T => (rho (fourier (1 : ℤ) t * q)) ^ 2)
    -- h_preimage : ∫ a in 0..0+T, f(↑a) = ∫ f d(volume)
    have h_haar := @AddCircle.integral_haarAddCircle T _ ℝ _ _
      (fun t => (rho (fourier (1 : ℤ) t * q)) ^ 2)
    -- h_haar : ∫ f d(haar) = T⁻¹ • ∫ f d(volume)
    -- So ∫ f d(volume) = T • ∫ f d(haar)
    -- And ∫_0^{0+T} g₁ = ∫ f d(volume) = T * ∫ f d(haar)
    calc ∫ x in (0:ℝ)..(0+T), g₁ x
        = ∫ t : AddCircle T, (rho (fourier (1 : ℤ) t * q)) ^ 2 := h_preimage
      _ = T * ∫ t : AddCircle T, (rho (fourier (1 : ℤ) t * q)) ^ 2
          ∂AddCircle.haarAddCircle := by
        -- ∫ f = T * ∫ f ∂haar  <==  ∫ f ∂haar = T⁻¹ • ∫ f
        rw [h_haar, smul_eq_mul]
        set V := ∫ t : AddCircle T, (rho (fourier (1 : ℤ) t * q)) ^ 2
        -- Goal: V = T * (T⁻¹ * V)
        rw [mul_comm T (T⁻¹ * V), mul_assoc, mul_comm V T, ← mul_assoc,
          inv_mul_cancel₀ hT_ne, one_mul]
  -- Step B: ∫ ρ(fourier(1)·q)² d(haar) ≥ ‖q‖²/8
  -- Use rotation invariance: fourier(1)(t) * q = ‖q‖ * fourier(1)(t + s)
  -- where s is chosen so that fourier(1)(s) = q/‖q‖
  have h_rot_avg : ∫ t : AddCircle T,
      (rho (fourier (1 : ℤ) t * q)) ^ 2
        ∂AddCircle.haarAddCircle ≥ ‖q‖ ^ 2 / 8 := by
    by_cases hq : q = 0
    · simp [hq, rho, norm_zero]
    · set r := ‖q‖
      have hr_pos : 0 < r := norm_pos_iff.mpr hq
      -- q = r * α where α = q/r, ‖α‖ = 1
      set α := (r : ℂ)⁻¹ * q
      have hα_norm : ‖α‖ = 1 := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr_pos]
        exact inv_mul_cancel₀ (ne_of_gt hr_pos)
      -- fourier(1)(t) * q = r * (fourier(1)(t) * α)
      have h_rw : ∀ t : AddCircle T,
          (rho (fourier (1 : ℤ) t * q)) ^ 2 =
          (rho (↑r * (fourier (1 : ℤ) t * α))) ^ 2 := by
        intro t; congr 2
        show fourier (1 : ℤ) t * q = ↑r * (fourier (1 : ℤ) t * α)
        simp only [α]
        have hr_ne' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
        field_simp
      simp_rw [h_rw]
      -- Find s : AddCircle such that fourier(1)(s) = α
      obtain ⟨s, hs⟩ := (AddCircle.homeomorphCircle hT_ne).surjective
        ⟨α, by
          rw [← SetLike.mem_coe, Submonoid.coe_unitSphere,
            Metric.mem_sphere, dist_zero_right]
          exact hα_norm⟩
      rw [AddCircle.homeomorphCircle_apply] at hs
      have hα_eq : (fourier (1 : ℤ) s : ℂ) = α := by
        simp only [fourier_apply, one_zsmul]
        exact congr_arg Subtype.val hs
      -- fourier(1)(t) * α = fourier(1)(t + s)
      have h_shift : ∀ t : AddCircle T,
          fourier (1 : ℤ) t * α = fourier (1 : ℤ) (t + s) := by
        intro t; rw [← hα_eq]
        -- fourier(n)(x+y) = fourier(n)(x) * fourier(n)(y)
        simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
      simp_rw [h_shift]
      -- ∫ f(t + s) d(haar) = ∫ f(t) d(haar) by translation invariance
      set F : AddCircle T → ℝ := fun u => (rho (↑r * fourier (1 : ℤ) u)) ^ 2
      change ∫ t, F (t + s) ∂AddCircle.haarAddCircle ≥ r ^ 2 / 8
      simp_rw [show ∀ t : AddCircle T, t + s = s + t from fun t => add_comm t s]
      rw [MeasureTheory.integral_add_left_eq_self]
      exact rotational_averaging_bound (norm_nonneg q)
  -- Step C: Combine
  rw [h_eq_haar_int]
  set I := ∫ t : AddCircle T, (rho (fourier (1 : ℤ) t * q)) ^ 2
    ∂AddCircle.haarAddCircle
  have : 1 / T * ((↑N)⁻¹ * (T * I)) = (↑N)⁻¹ * I := by field_simp
  rw [this]
  have hN_inv : (0 : ℝ) < (↑N)⁻¹ := inv_pos.mpr hN_pos
  calc (↑N)⁻¹ * I ≥ (↑N)⁻¹ * (‖q‖ ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left h_rot_avg.le hN_inv.le
    _ = ‖q‖ ^ 2 / (8 * ↑N) := by field_simp

/-- 4.1d: Assembly.
    Integrates the pointwise bound `rho_sq_lower` on each
    interval, applies `frozen_rotation`, and sums using
    `parseval_partition`.

    Proof:
    Step 1: On I_k, for each t:
      ρ(P(t))² = ρ(fourier(N)(t)·Q(t))²
      ≥ (1/2)ρ(fourier(N)(t)·q_k)² - ‖Q(t)-q_k‖²
      (by rho_sq_lower with α = fourier(N)(t), w = Q(t), z = q_k)
    Step 2: Integrate over I_k and divide by T:
      (1/T)∫_{I_k} ρ(P)² ≥ (1/2)(1/T)∫_{I_k} ρ(fourier(N)·q_k)²
                              - (1/T)∫_{I_k} ‖Q-q_k‖²
    Step 3: By frozen_rotation: (1/T)∫_{I_k} ρ(fourier(N)·q_k)² ≥ ‖q_k‖²/(8N)
    Step 4: Sum over k:
      ∫ ρ(P)² d(haar) ≥ (1/2)·(1/(8N))·∑‖q_k‖² - totalDelta
      = (1/16)·(1/N)·∑‖q_k‖² - totalDelta
    Step 5: By parseval_partition: (1/N)∑‖q_k‖² = C - δ
      So: ≥ (1/16)(C - δ) - δ = C/16 - (17/16)δ -/
private lemma assembly {N L : ℕ} (hN : 1 ≤ N)
    (b : Fin L → ℂ) (P : AddCircle T → ℂ)
    (hP : P = fun t =>
      ∑ m : Fin L,
        b m * fourier ((N + m.val : ℕ) : ℤ) t) :
    ∫ t : AddCircle T,
        (rho (P t)) ^ 2
          ∂AddCircle.haarAddCircle ≥
      (1 / 16) * circleNormSq (slowFactor b) -
        (17 / 16) * totalDelta b N := by
  -- Use haar_eq_sum_intervals to decompose the Haar integral
  have hP_cont : Continuous P := by
    rw [hP]; exact continuous_finsetSum _ (fun m _ =>
      (continuous_const.mul ((fourier _).continuous)))
  have hρP_cont : Continuous (fun t => (rho (P t)) ^ 2) :=
    (rho_continuous.comp hP_cont).pow 2
  rw [haar_eq_sum_intervals hN hρP_cont]
  -- Decompose into per-interval bounds
  have hT_pos : (0 : ℝ) < T := T_pos
  have hN_pos : (0 : ℝ) < (↑N : ℝ) := Nat.cast_pos.mpr (by omega)
  -- On each I_k: use rho_sq_lower pointwise, then integrate
  -- Key: P(t) = fourier(N)(t) * Q(t), and we compare Q(t) with q_k
  have hPQ := P_eq_fourier_mul_Q b P hP
  have h_per_k : ∀ k : Fin N,
      (1 / T) * ∫ t in iLeft N k.val..iLeft N (k.val + 1),
        (rho (P (↑t : AddCircle T))) ^ 2 ≥
      (1 / 2) * (‖qAvg b N k‖ ^ 2 / (8 * ↑N)) -
        (1 / T) * ∫ t in iLeft N k.val..iLeft N (k.val + 1),
          ‖slowFactor b (↑t : AddCircle T) - qAvg b N k‖ ^ 2 := by
    intro k
    have hab : iLeft N k.val ≤ iLeft N (k.val + 1) := le_of_lt (iLeft_lt_iLeft N hN k.val)
    -- Pointwise bound
    have h_pw : ∀ t ∈ Set.Icc (iLeft N k.val) (iLeft N (k.val + 1)),
        (1 / 2) * (rho (fourier (N : ℤ) (↑t : AddCircle T) * qAvg b N k)) ^ 2 -
          ‖slowFactor b (↑t : AddCircle T) - qAvg b N k‖ ^ 2 ≤
        (rho (P (↑t : AddCircle T))) ^ 2 := by
      intro t _
      rw [hPQ]; change _ ≤ (rho (fourier (↑↑N) ↑t * slowFactor b ↑t)) ^ 2
      have := rho_sq_lower (fourier (N : ℤ) (↑t : AddCircle T))
        (slowFactor b (↑t : AddCircle T)) (qAvg b N k) (norm_fourier_apply _ _)
      linarith
    -- Integrate the pointwise bound
    have hT_inv_pos : (0 : ℝ) < 1 / T := div_pos one_pos hT_pos
    have hi1 : IntervalIntegrable (fun t => (rho (P (↑t : AddCircle T))) ^ 2)
        volume (iLeft N k.val) (iLeft N (k.val + 1)) :=
      (hρP_cont.comp (AddCircle.continuous_mk' T)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t =>
        (1/2) * (rho (fourier (N : ℤ) (↑t : AddCircle T) * qAvg b N k)) ^ 2 -
          ‖slowFactor b (↑t : AddCircle T) - qAvg b N k‖ ^ 2)
        volume (iLeft N k.val) (iLeft N (k.val + 1)) := by
      apply IntervalIntegrable.sub
      · apply IntervalIntegrable.const_mul
        exact ((rho_continuous.comp (((fourier _).continuous.comp
            (AddCircle.continuous_mk' T)).mul continuous_const)).pow 2).intervalIntegrable _ _
      · exact ((((slowFactor_continuous b).comp (AddCircle.continuous_mk' T)).sub
            continuous_const).norm.pow 2).intervalIntegrable _ _
    have h_int_bound := intervalIntegral.integral_mono_on hab hi2 hi1 h_pw
    -- Split the integral on the RHS
    have hi_rho : IntervalIntegrable (fun t =>
        (rho (fourier (N : ℤ) (↑t : AddCircle T) * qAvg b N k)) ^ 2)
        volume (iLeft N k.val) (iLeft N (k.val + 1)) :=
      ((rho_continuous.comp (((fourier _).continuous.comp
          (AddCircle.continuous_mk' T)).mul continuous_const)).pow 2).intervalIntegrable _ _
    have hi_norm : IntervalIntegrable (fun t =>
        ‖slowFactor b (↑t : AddCircle T) - qAvg b N k‖ ^ 2)
        volume (iLeft N k.val) (iLeft N (k.val + 1)) :=
      ((((slowFactor_continuous b).comp (AddCircle.continuous_mk' T)).sub
          continuous_const).norm.pow 2).intervalIntegrable _ _
    -- Name the key integrals first
    set A := ∫ t in iLeft N k.val..iLeft N (k.val + 1),
      (rho (fourier (N : ℤ) (↑t : AddCircle T) * qAvg b N k)) ^ 2 with hA_def
    set B := ∫ t in iLeft N k.val..iLeft N (k.val + 1),
      ‖slowFactor b (↑t : AddCircle T) - qAvg b N k‖ ^ 2 with hB_def
    have h_split : ∫ t in iLeft N k.val..iLeft N (k.val + 1),
        ((1/2) * (rho (fourier (N : ℤ) (↑t : AddCircle T) * qAvg b N k)) ^ 2 -
          ‖slowFactor b (↑t : AddCircle T) - qAvg b N k‖ ^ 2) =
      (1/2) * A - B := by
      have h1 := intervalIntegral.integral_sub (hi_rho.const_mul (1/2)) hi_norm
      have h2 : ∫ t in iLeft N k.val..iLeft N (k.val + 1),
          (1/2) * (rho (fourier (N : ℤ) (↑t : AddCircle T) * qAvg b N k)) ^ 2 =
        (1/2) * ∫ t in iLeft N k.val..iLeft N (k.val + 1),
          (rho (fourier (N : ℤ) (↑t : AddCircle T) * qAvg b N k)) ^ 2 :=
        intervalIntegral.integral_const_mul _ _
      simp only [hA_def, hB_def] at h1 h2 ⊢
      linarith
    rw [h_split] at h_int_bound
    -- Multiply by 1/T
    have h_mul := mul_le_mul_of_nonneg_left h_int_bound hT_inv_pos.le
    -- Use frozen_rotation for the first term
    have h_frozen := frozen_rotation hN b k
    -- Expand 1/T * (1/2 * A - B) = 1/2 * (1/T * A) - 1/T * B
    have h_expand : 1 / T * (1 / 2 * A - B) = 1 / 2 * (1 / T * A) - 1 / T * B := by ring
    rw [h_expand] at h_mul
    linarith
  -- Sum over k
  have h_sum : (1 / T) • ∑ k : Fin N,
      ∫ t in iLeft N k.val..iLeft N (k.val + 1),
        (rho (P (↑t : AddCircle T))) ^ 2 ≥
    (1 / 16) * ((1 / ↑N) * ∑ k : Fin N, ‖qAvg b N k‖ ^ 2) -
      totalDelta b N := by
    rw [smul_eq_mul, Finset.mul_sum]
    have h_sum_ge := Finset.sum_le_sum (s := Finset.univ) (fun k _ => (h_per_k k).le)
    -- RHS of h_sum_ge is ∑_k [(1/2)(‖q_k‖²/(8N)) - (1/T)∫‖Q-q_k‖²]
    -- = (1/16N)∑‖q_k‖² - totalDelta
    have h_rhs_eq : ∑ k : Fin N,
        ((1/2) * (‖qAvg b N k‖ ^ 2 / (8 * ↑N)) -
          (1/T) * ∫ t in iLeft N k.val..iLeft N (k.val + 1),
            ‖slowFactor b (↑t : AddCircle T) - qAvg b N k‖ ^ 2) =
      (1/16) * ((1/↑N) * ∑ k : Fin N, ‖qAvg b N k‖ ^ 2) -
        totalDelta b N := by
      rw [Finset.sum_sub_distrib]
      congr 1
      · -- Goal: ∑ 1/2 * (‖q_k‖² / (8N)) = 1/16 * (1/N * ∑ ‖q_k‖²)
        simp_rw [show ∀ k : Fin N, (1:ℝ) / 2 * (‖qAvg b N k‖ ^ 2 / (8 * ↑N)) =
            (1 / (16 * ↑N)) * ‖qAvg b N k‖ ^ 2 from fun k => by
            have : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos; field_simp; ring]
        rw [← Finset.mul_sum]
        have : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos; field_simp
      · unfold totalDelta; rw [Finset.mul_sum]
    linarith
  -- Apply parseval_partition
  have h_parseval := parseval_partition hN b
  -- h_parseval: C = (1/N)∑|q_k|² + δ, so (1/N)∑|q_k|² = C - δ
  linarith

/-! ## Auxiliary -/

private lemma circleNormSq_nonneg
    (f : AddCircle T → ℂ) :
    0 ≤ circleNormSq f := by
  unfold circleNormSq; apply integral_nonneg; intro
  positivity

/-! ## Core lower bound

Combines assembly + Poincaré to get:
  ∫ ρ(P)² d(haar) ≥ circleNormSq(Q) / 32.

The arithmetic reduces to:
  136π²(L−1)² ≤ N² (under 1343L² ≤ N²).

Since `136π² ≈ 1342.27`, we need `⌈136π²⌉ = 1343`.
The hypothesis `1343 * L^2 ≤ N^2` implies `136π²(L-1)² ≤ 136π²L² ≤ 1343L² ≤ N²`.
-/

-- Numerical fact: 136 * π² < 1343
private lemma pi_sq_bound : 136 * Real.pi ^ 2 < 1343 := by
  have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [sq_nonneg (3.141593 - Real.pi)]

private lemma rho_integral_lower_bound {N L : ℕ}
    (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hNL : 1343 * L ^ 2 ≤ N ^ 2)
    (b : Fin L → ℂ) (P : AddCircle T → ℂ)
    (hP : P = fun t =>
      ∑ m : Fin L,
        b m * fourier ((N + m.val : ℕ) : ℤ) t) :
    ∫ t : AddCircle T,
        (rho (P t)) ^ 2
          ∂AddCircle.haarAddCircle ≥
      circleNormSq (slowFactor b) / 32 := by
  have h_asm := assembly hN b P hP
  have h_poi := poincare_bound hN hL b
  have h_nn := circleNormSq_nonneg (slowFactor b)
  set C := circleNormSq (slowFactor b)
  set δ := totalDelta b N
  -- From assembly: ∫ρ² ≥ C/16 − (17/16)δ
  -- From poincare: δ ≤ r·C where r = 4π²(L-1)²/N²
  -- Need: C/16 - (17/16)·r·C ≥ C/32
  --   <=>  (17/16)·r ≤ 1/32
  --   <=>  17·r ≤ 1/2
  --   <=>  68π²(L-1)²/N² ≤ 1/2
  --   <=>  136π²(L-1)² ≤ N²
  -- Since (L-1)² ≤ L² and 136π² < 1343: 136π²(L-1)² ≤ 1343L² ≤ N²
  have hpi2 := pi_sq_bound
  have hL_real : (1 : ℝ) ≤ (↑L : ℝ) := Nat.one_le_cast.mpr hL
  have hL_cast : (0 : ℝ) ≤ (↑L : ℝ) - 1 := by linarith
  have hN_pos : (0 : ℝ) < (↑N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN2_pos : (0 : ℝ) < (↑N : ℝ) ^ 2 := by positivity
  have hNL_cast : (1343 : ℝ) * (↑L : ℝ) ^ 2 ≤ (↑N : ℝ) ^ 2 := by
    have : (1343 * L ^ 2 : ℕ) ≤ (N ^ 2 : ℕ) := hNL
    exact_mod_cast this
  -- Key: 4π²(L-1)² ≤ N²/34
  have h_rate_bound : 34 * (4 * Real.pi ^ 2 * (↑L - 1) ^ 2) ≤ (↑N : ℝ) ^ 2 := by
    have hLm1_sq : ((↑L : ℝ) - 1) ^ 2 ≤ (↑L : ℝ) ^ 2 := by apply sq_le_sq' <;> linarith
    -- 34 * 4π² * (L-1)² ≤ 136π² * L² < 1343 * L² ≤ N²
    nlinarith [sq_nonneg Real.pi, sq_nonneg (↑L : ℝ)]
  -- r·C ≤ C/34 where r = 4π²(L-1)²/N²
  have h_key : 4 * Real.pi ^ 2 * (↑L - 1) ^ 2 / ↑N ^ 2 * C ≤ C / 34 := by
    have h1 : 4 * Real.pi ^ 2 * (↑L - 1) ^ 2 / ↑N ^ 2 ≤ 1 / 34 := by
      rw [div_le_div_iff₀ hN2_pos (by norm_num : (0:ℝ) < 34)]
      linarith
    calc 4 * Real.pi ^ 2 * (↑L - 1) ^ 2 / ↑N ^ 2 * C
        ≤ (1 / 34) * C := by nlinarith
      _ = C / 34 := by ring
  -- Combine: ∫ρ² ≥ C/16 - (17/16)δ ≥ C/16 - (17/16)·(C/34) = C/16 - C/32 = C/32
  linarith

/-! ## Main theorem -/

/-- **Theorem 4.1**: High-frequency band estimate.
    For N ≥ 1, L ≥ 1, 1343·L² ≤ N², and
    P(t) = ∑ b(m)·fourier(N+m)(t):
      circleNormSq(P) ≤ 32 · ∫ ρ(P)² d(haar). -/
theorem high_freq_band_estimate {N L : ℕ}
    (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hNL : 1343 * L ^ 2 ≤ N ^ 2)
    (b : Fin L → ℂ) (P : AddCircle T → ℂ)
    (hP : P = fun t =>
      ∑ m : Fin L,
        b m * fourier ((N + m.val : ℕ) : ℤ) t) :
    circleNormSq P ≤ 32 *
      (∫ t : AddCircle T,
        (rho (P t)) ^ 2
          ∂AddCircle.haarAddCircle) := by
  have h_eq := circleNormSq_P_eq_Q b P hP
  have h_lb :=
    rho_integral_lower_bound hN hL hNL b P hP
  linarith

end FockSPR
