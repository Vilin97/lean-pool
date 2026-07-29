/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.Existence
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.GammaStrip

/-!
# Analytic control of the completed Dedekind zeta function  (SP1-AC leaf A2)

Uniform vertical-strip bounds for the Hecke pair's Mellin transforms, from the triangle
inequality applied to the strong pair's full-line Mellin representation:

* `norm_heckeΛ₀_le` — `‖Λ₀(s)‖` is at most the norm-integral at `Re s`;
* `integrable_heckeΛ₀_norm` — those norm-integrals converge at every real exponent;
* `exists_heckeΛ₀_strip_bound` — `‖Λ₀‖` is bounded on every vertical strip, uniformly
  in the imaginary direction (the `x^{σ-1} ≤ x^{a-1} + x^{b-1}` endpoint trick).

Downstream (per `.mathlib-quality/decomposition-sp1ac.md`): Λ- and
`H(s) = s(s-1)Λ_K(s)`-versions, the ζ_K convexity bounds (with `GammaStrip`), Jensen
zero-counting, and the Landau local partial fractions.
-/

namespace DedekindResidue

@[expose] public section

open Complex MeasureTheory NumberField NumberField.InfinitePlace
open scoped Real

variable (K : Type*) [Field K] [NumberField K]

/-- Elementary norm bound `‖σ + t·I‖ ≤ σ + |t|` for a nonnegative real abscissa `σ`;
the peeling step behind the vertical-strip Γ-bounds. -/
theorem norm_ofReal_add_mul_I_le (σ t : ℝ) (hσ : 0 ≤ σ) :
    ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ σ + |t| := by
  refine le_trans (norm_add_le _ _) (le_of_eq ?_)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hσ]

/-- Half-angle exponential rewrite `e^{-π|t/2|/2} = e^{-π|t|/4}`, converting the
`Γ(·/2)` decay rate into the `Γℝ`/`Γℂ` envelope rate. -/
theorem exp_neg_pi_abs_half_div_two (t : ℝ) :
    Real.exp (-(π * |t/2|) / 2) = Real.exp (-(π * |t|) / 4) := by
  congr 1
  rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
  ring

/-- Pointwise Mellin triangle inequality for the entire completed theta transform:
`‖Λ₀(s)‖` is at most the norm-integral at the real part. -/
theorem norm_heckeΛ₀_le (s : ℂ) :
    ‖(heckeFEPair K).Λ₀ s‖
      ≤ ∫ x in Set.Ioi (0:ℝ), x ^ (s.re - 1) * ‖(heckeFEPair K).f_modif x‖ := by
  rw [WeakFEPair.Λ₀, mellin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

/-- The norm-integrals converge at every real exponent (the strong pair has full-line
Mellin convergence). -/
theorem integrable_heckeΛ₀_norm (a : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖)
      (Set.Ioi 0) := by
  have hconv : MellinConvergent ((heckeFEPair K).f_modif) (a : ℂ) :=
    ((heckeFEPair K).toStrongFEPair.hasMellin (a : ℂ)).1
  have hnn : IntegrableOn
      (fun x : ℝ => ‖((x:ℂ) ^ ((a:ℂ) - 1) • (heckeFEPair K).f_modif x)‖)
      (Set.Ioi 0) := hconv.norm
  refine hnn.congr_fun (fun x hx => ?_) measurableSet_Ioi
  show ‖((x:ℂ) ^ ((a:ℂ) - 1) • (heckeFEPair K).f_modif x)‖
    = x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

/-- **AC-A2: uniform vertical-strip bound for `Λ₀`** — on any strip `a ≤ Re s ≤ b`,
`‖Λ₀(s)‖` is bounded by a constant depending only on the strip (and `K`), uniformly
in the imaginary direction. -/
theorem exists_heckeΛ₀_strip_bound (a b : ℝ) :
    ∃ B : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖(heckeFEPair K).Λ₀ s‖ ≤ B := by
  refine ⟨(∫ x in Set.Ioi (0:ℝ), x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖)
    + ∫ x in Set.Ioi (0:ℝ), x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖, ?_⟩
  intro s ha hb
  refine le_trans (norm_heckeΛ₀_le K s) ?_
  have hmono : ∀ x ∈ Set.Ioi (0:ℝ),
      x ^ (s.re - 1) * ‖(heckeFEPair K).f_modif x‖
        ≤ x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖
          + x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖ := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    rcases le_or_gt x 1 with hx1 | hx1
    · have h1 : x ^ (s.re - 1) ≤ x ^ (a - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
      have h2 : (0:ℝ) ≤ x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖ := by positivity
      nlinarith [norm_nonneg ((heckeFEPair K).f_modif x), Real.rpow_nonneg hx0.le (s.re - 1)]
    · have h1 : x ^ (s.re - 1) ≤ x ^ (b - 1) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) (by linarith)
      have h2 : (0:ℝ) ≤ x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖ := by positivity
      nlinarith [norm_nonneg ((heckeFEPair K).f_modif x), Real.rpow_nonneg hx0.le (s.re - 1)]
  calc (∫ x in Set.Ioi (0:ℝ), x ^ (s.re - 1) * ‖(heckeFEPair K).f_modif x‖)
      ≤ ∫ x in Set.Ioi (0:ℝ),
          (x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖
            + x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖) :=
        setIntegral_mono_on (integrable_heckeΛ₀_norm K s.re)
          ((integrable_heckeΛ₀_norm K a).add (integrable_heckeΛ₀_norm K b))
          measurableSet_Ioi hmono
    _ = (∫ x in Set.Ioi (0:ℝ), x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖)
          + ∫ x in Set.Ioi (0:ℝ), x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖ :=
        integral_add (integrable_heckeΛ₀_norm K a) (integrable_heckeΛ₀_norm K b)

/-- **AC-A2-ii: polynomial strip bound for the entire completed zeta**
`H(s) = s(s-1)Λ_K(s)`: on every vertical strip, `‖H(s)‖ ≤ B·(1+‖s‖)²` uniformly in
the imaginary direction. This is the growth input for Jensen counting and the
contour estimates. -/
theorem exists_completedDedekindZetaEntire_strip_bound (a b : ℝ) (hab : a ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖completedDedekindZetaEntire K s‖ ≤ B * (1 + ‖s‖)^2 := by
  obtain ⟨B₀, hB₀⟩ := exists_heckeΛ₀_strip_bound K (a/2) (b/2)
  have hB₀0 : 0 ≤ B₀ := by
    refine le_trans (norm_nonneg ((heckeFEPair K).Λ₀ ((a/2 : ℝ) : ℂ))) (hB₀ _ ?_ ?_)
    · simp
    · simp
      linarith
  refine ⟨‖(((heckeAdjust K : ℝ) : ℂ))⁻¹‖
    * (B₀ + 2 * ‖(heckeFEPair K).f₀‖ + 2 * ‖(heckeFEPair K).g₀‖),
    by positivity, fun s ha hb => ?_⟩
  have hs2 : (s / 2).re = s.re / 2 := by
    rw [show s / 2 = ((1/2 : ℝ) : ℂ) * s by push_cast; ring, Complex.re_ofReal_mul]
    ring
  have hΛ : ‖(heckeFEPair K).Λ₀ (s / 2)‖ ≤ B₀ :=
    hB₀ (s/2) (by rw [hs2]; linarith) (by rw [hs2]; linarith)
  have h1s : ‖s‖ ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have h1s1 : ‖s - 1‖ ≤ 1 + ‖s‖ := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 1 + ‖s‖ := by rw [norm_one]; ring
  have hone : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hmain : ‖s * (s - 1) * (heckeFEPair K).Λ₀ (s / 2)
      - 2 * (s - 1) * (heckeFEPair K).f₀ + 2 * s * (heckeFEPair K).g₀‖
      ≤ (1 + ‖s‖)^2 * (B₀ + 2 * ‖(heckeFEPair K).f₀‖ + 2 * ‖(heckeFEPair K).g₀‖) := by
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add_left (norm_sub_le _ _) _) ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    have hsq : 1 + ‖s‖ ≤ (1 + ‖s‖)^2 := by nlinarith [norm_nonneg s]
    have e1 : ‖s‖ * ‖s - 1‖ * ‖(heckeFEPair K).Λ₀ (s / 2)‖ ≤ (1 + ‖s‖)^2 * B₀ := by
      have hss : ‖s‖ * ‖s - 1‖ ≤ (1 + ‖s‖)^2 := by
        nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
      exact mul_le_mul hss hΛ (norm_nonneg _) (by positivity)
    have e2 : 2 * ‖s - 1‖ * ‖(heckeFEPair K).f₀‖
        ≤ (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).f₀‖) := by
      calc 2 * ‖s - 1‖ * ‖(heckeFEPair K).f₀‖
          = ‖s - 1‖ * (2 * ‖(heckeFEPair K).f₀‖) := by ring
        _ ≤ (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).f₀‖) :=
            mul_le_mul_of_nonneg_right (h1s1.trans hsq) (by positivity)
    have e3 : 2 * ‖s‖ * ‖(heckeFEPair K).g₀‖
        ≤ (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).g₀‖) := by
      calc 2 * ‖s‖ * ‖(heckeFEPair K).g₀‖
          = ‖s‖ * (2 * ‖(heckeFEPair K).g₀‖) := by ring
        _ ≤ (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).g₀‖) :=
            mul_le_mul_of_nonneg_right (h1s.trans hsq) (by positivity)
    have hdist : (1 + ‖s‖)^2 * (B₀ + 2 * ‖(heckeFEPair K).f₀‖ + 2 * ‖(heckeFEPair K).g₀‖)
        = (1 + ‖s‖)^2 * B₀ + (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).f₀‖)
          + (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).g₀‖) := by ring
    rw [hdist]
    linarith
  rw [completedDedekindZetaEntire, norm_mul]
  calc ‖(((heckeAdjust K : ℝ) : ℂ))⁻¹‖
      * ‖s * (s - 1) * (heckeFEPair K).Λ₀ (s / 2)
          - 2 * (s - 1) * (heckeFEPair K).f₀ + 2 * s * (heckeFEPair K).g₀‖
      ≤ ‖(((heckeAdjust K : ℝ) : ℂ))⁻¹‖
        * ((1 + ‖s‖)^2 * (B₀ + 2 * ‖(heckeFEPair K).f₀‖ + 2 * ‖(heckeFEPair K).g₀‖)) :=
        mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
    _ = ‖(((heckeAdjust K : ℝ) : ℂ))⁻¹‖
        * (B₀ + 2 * ‖(heckeFEPair K).f₀‖ + 2 * ‖(heckeFEPair K).g₀‖) * (1 + ‖s‖)^2 := by
        ring

/-- **AC-A4 center lower bound**: far enough right, the Dedekind zeta function is at
least `1/2` in modulus — the Dirichlet tail `∑_{n≥2} a_n n^{-σ}` decays like `2^{-σ}`
once it converges, so it is eventually below `1/2`. -/
theorem exists_re_norm_dedekindZeta_ge_half :
    ∃ A : ℝ, 2 ≤ A ∧ ∀ s : ℂ, A ≤ s.re → 1/2 ≤ ‖dedekindZeta K s‖ := by
  set f : ℕ → ℂ := fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)
    with hf
  have hsum2 : LSeriesSummable f 2 := by
    have h := count_LSeriesSummable K (by norm_num : (1:ℝ) < 2)
    have hfe : (fun n : ℕ =>
        ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) = f := by
      funext n
      rw [hf]
      push_cast
      rfl
    rw [hfe] at h
    exact_mod_cast h
  set T : ℝ := ∑' n : ℕ, ‖LSeries.term f 2 n‖ with hT
  have hT0 : 0 ≤ T := tsum_nonneg (fun n => norm_nonneg _)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, T * (1/2)^m ≤ 1/2 := by
    rcases eq_or_lt_of_le hT0 with h0 | hpos
    · exact ⟨0, by rw [← h0]; norm_num⟩
    · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
        (show (0:ℝ) < 1/(2*T) by positivity) (by norm_num : (1:ℝ)/2 < 1)
      refine ⟨m, ?_⟩
      have := mul_le_mul_of_nonneg_left hm.le hT0
      calc T * (1/2)^m ≤ T * (1/(2*T)) := this
        _ = 1/2 := by field_simp
  refine ⟨2 + m, by linarith [Nat.cast_nonneg (α := ℝ) m], fun s hs => ?_⟩
  have hσ2 : (2:ℝ) ≤ s.re := by
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hsummS : LSeriesSummable f s := hsum2.of_re_le_re (by simpa using hσ2)
  have hterm1 : LSeries.term f s 1 = 1 := by
    rw [LSeries.term_def]
    simp [hf]
  have hζ : dedekindZeta K s
      = 1 + ∑' n : ℕ, ite (n = 1) 0 (LSeries.term f s n) := by
    rw [dedekindZeta, LSeries]
    rw [show (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) = f
      from rfl]
    rw [hsummS.tsum_eq_add_tsum_ite 1, hterm1]
  -- pointwise tail comparison against the exponent-2 terms
  have hpoint : ∀ n : ℕ, ‖ite (n = 1) 0 (LSeries.term f s n)‖
      ≤ (1/2)^m * ‖LSeries.term f 2 n‖ := by
    intro n
    rcases eq_or_ne n 1 with rfl | hn1
    · simp
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [if_neg hn1, LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn0, if_neg hn0,
      show ((2:ℂ)).re = (2:ℝ) by norm_num]
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
    have hnpos : (0:ℝ) < n := by linarith
    have hkey : (n:ℝ)^(2:ℝ) * (2:ℝ)^(m:ℝ) ≤ (n:ℝ)^(s.re) := by
      have h1 : (2:ℝ)^(m:ℝ) ≤ (n:ℝ)^(s.re - 2) := by
        calc (2:ℝ)^(m:ℝ) ≤ (2:ℝ)^(s.re - 2) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ ≤ (n:ℝ)^(s.re - 2) := Real.rpow_le_rpow (by norm_num) hn2 (by linarith)
      calc (n:ℝ)^(2:ℝ) * (2:ℝ)^(m:ℝ)
          ≤ (n:ℝ)^(2:ℝ) * (n:ℝ)^(s.re - 2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (n:ℝ)^(s.re) := by
            rw [← Real.rpow_add hnpos]
            ring_nf
    have hhalf : ((1:ℝ)/2)^m * ((2:ℝ)^(m:ℝ)) = 1 := by
      rw [← Real.rpow_natCast ((1:ℝ)/2) m,
        ← Real.mul_rpow (by norm_num) (by norm_num)]
      norm_num
    calc ‖f n‖ / (n:ℝ)^(s.re)
        ≤ ‖f n‖ / ((n:ℝ)^(2:ℝ) * (2:ℝ)^(m:ℝ)) := by
          gcongr
      _ = (1/2)^m * (‖f n‖ / (n:ℝ)^(2:ℝ)) := by
          rw [← div_div, div_eq_mul_inv (‖f n‖ / (n:ℝ)^(2:ℝ)), mul_comm]
          congr 1
          exact (eq_inv_of_mul_eq_one_left hhalf).symm
  -- summability of the pieces
  have hnormS : Summable (fun n : ℕ => ‖ite (n = 1) 0 (LSeries.term f s n)‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsummS.norm
    rcases eq_or_ne n 1 with rfl | hn1
    · simp
    · rw [if_neg hn1]
  have hcompar : Summable (fun n : ℕ => (1/2:ℝ)^m * ‖LSeries.term f 2 n‖) :=
    (hsum2.norm).mul_left _
  have hRbound : ‖∑' n : ℕ, ite (n = 1) 0 (LSeries.term f s n)‖ ≤ T * (1/2)^m := by
    refine le_trans (norm_tsum_le_tsum_norm hnormS) ?_
    calc (∑' n : ℕ, ‖ite (n = 1) 0 (LSeries.term f s n)‖)
        ≤ ∑' n : ℕ, (1/2:ℝ)^m * ‖LSeries.term f 2 n‖ :=
          hnormS.tsum_le_tsum hpoint hcompar
      _ = (1/2)^m * T := by rw [tsum_mul_left]
      _ = T * (1/2)^m := by ring
  rw [hζ]
  set R : ℂ := ∑' n : ℕ, ite (n = 1) 0 (LSeries.term f s n) with hR
  have h1R : (1:ℝ) ≤ ‖(1:ℂ) + R‖ + ‖R‖ := by
    calc (1:ℝ) = ‖(1:ℂ)‖ := by norm_num
      _ = ‖((1:ℂ) + R) + (-R)‖ := by ring_nf
      _ ≤ ‖(1:ℂ) + R‖ + ‖-R‖ := norm_add_le _ _
      _ = ‖(1:ℂ) + R‖ + ‖R‖ := by rw [norm_neg]
  linarith [le_trans hRbound hm]

/-- Decaying upper bound for `Γℝ` on `1 ≤ σ ≤ 2`, `|t| ≥ 2`:
`‖Γℝ(σ+it)‖ ≤ √(12π)·(1+|t|)·e^{-π|t|/4}`. -/
theorem norm_Gammaℝ_le {σ t : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 4) := by
  rw [Complex.Gammaℝ_def, norm_mul]
  have hπ : ‖(π : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-((σ : ℂ) + (t : ℂ) * Complex.I) / 2).re = -σ/2 := by
      rw [show -((σ : ℂ) + (t : ℂ) * Complex.I) / 2
          = ((-σ/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
      simp
    rw [hre]
    calc π ^ (-σ/2 : ℝ) ≤ π ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = 1 := Real.rpow_zero π
  have harg : ((σ : ℂ) + (t : ℂ) * Complex.I) / 2
      = ((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have ht2 : 1 ≤ |t/2| := by
    rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
    linarith
  have hΓ : ‖Complex.Gamma (((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖
      ≤ Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 4) := by
    rw [harg]
    refine le_trans (norm_Gamma_le_mul_exp (σ := σ/2) (t := t/2)
      (by linarith) (by linarith) ht2) ?_
    have hnorm : ‖((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I‖ ≤ 1 + |t| := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have hs2 : |σ/2| ≤ 1 := by
        rw [abs_div, show |(2:ℝ)| = 2 by norm_num,
          abs_of_pos (by linarith : (0:ℝ) < σ)]
        linarith
      have ht2' : |t/2| ≤ |t| := by
        rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
        linarith [abs_nonneg t]
      linarith
    rw [exp_neg_pi_abs_half_div_two t]
    gcongr
  calc ‖(π : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖
      * ‖Complex.Gamma (((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖
      ≤ 1 * (Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 4)) :=
        mul_le_mul hπ hΓ (norm_nonneg _) (by norm_num)
    _ = Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 4) := by ring

/-- Decaying upper bound for `Γℂ` on `1 ≤ σ ≤ 2`, `|t| ≥ 2`:
`‖Γℂ(σ+it)‖ ≤ 8√(12π)·(1+|t|)²·e^{-π|t|/2}`. -/
theorem norm_Gammaℂ_le {σ t : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 8 * Real.sqrt (12 * π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2) := by
  rw [Complex.Gammaℂ_def, norm_mul, norm_mul]
  have ht1 : 1 ≤ |t| := by linarith
  have h1t : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hsq : (0:ℝ) ≤ Real.sqrt (12*π) := Real.sqrt_nonneg _
  have he : (0:ℝ) < Real.exp (-(π * |t|)/2) := Real.exp_pos _
  have h2π : ‖((2:ℂ) * π) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1 := by
    rw [show ((2:ℂ) * π) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hre : (-((σ : ℂ) + (t : ℂ) * Complex.I)).re = -σ := by simp
    rw [hre]
    calc (2*π) ^ (-σ : ℝ) ≤ (2*π) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = 1 := Real.rpow_zero _
  have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
  have hznorm : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ 2 * (1 + |t|) := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < σ)]
    nlinarith [abs_nonneg t]
  have hΓ : ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 4 * Real.sqrt (12 * π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2) := by
    rcases le_or_gt σ (3/2) with hσ | hσ
    · refine le_trans (norm_Gamma_le_mul_exp (σ := σ) (t := t) (by linarith) hσ ht1) ?_
      have hstep : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ 4 * (1 + |t|)^2 := by
        refine le_trans hznorm ?_
        nlinarith
      calc Real.sqrt (12*π) * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ * Real.exp (-(π * |t|)/2)
          ≤ Real.sqrt (12*π) * (4 * (1 + |t|)^2) * Real.exp (-(π * |t|)/2) := by
            gcongr
        _ = 4 * Real.sqrt (12*π) * (1 + |t|)^2 * Real.exp (-(π * |t|)/2) := by ring
    · have hne : ((σ : ℂ) + (t : ℂ) * Complex.I) - 1 ≠ 0 := by
        intro h0
        have := congrArg Complex.im h0
        simp at this
        rw [this] at ht1
        norm_num at ht1
      have hrec : Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
          = (((σ : ℂ) + (t : ℂ) * Complex.I) - 1)
            * Complex.Gamma (((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
        have h := Complex.Gamma_add_one (((σ : ℂ) + (t : ℂ) * Complex.I) - 1) hne
        rw [sub_add_cancel] at h
        rw [h]
        congr 2
        push_cast
        ring
      rw [hrec, norm_mul]
      have hfac : ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ≤ 3 * (1 + |t|) := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_one]
        linarith [hznorm]
      have hbase := norm_Gamma_le_mul_exp (σ := σ - 1) (t := t)
        (by linarith) (by linarith) ht1
      have hn1 : ‖((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + |t| := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < σ - 1)]
        linarith
      calc ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖
          * ‖Complex.Gamma (((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (3 * (1 + |t|))
            * (Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 2)) := by
            refine mul_le_mul hfac (le_trans hbase ?_) (norm_nonneg _) (by positivity)
            gcongr
        _ ≤ 4 * Real.sqrt (12 * π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2) := by
            nlinarith [mul_nonneg (mul_nonneg hsq (by nlinarith : (0:ℝ) ≤ (1+|t|)^2)) he.le]
  calc ‖(2:ℂ)‖ * ‖((2:ℂ) * π) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2 * 1 * (4 * Real.sqrt (12 * π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2)) := by
        rw [h2n]
        refine mul_le_mul (by nlinarith [norm_nonneg (((2:ℂ) * π)
          ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))]) hΓ (norm_nonneg _) (by norm_num)
    _ = 8 * Real.sqrt (12 * π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2) := by ring

/-- **Decaying upper for the archimedean factor** on `1 ≤ σ ≤ 2`, `|t| ≥ 2`:
`‖γ_K(σ+it)‖ ≤ C_K·(1+|t|)^{n}·e^{-nπ|t|/4}` with `n = r₁ + 2r₂` — the envelope rate
matched by the lower bounds (`Γℝ` decays at `π|t|/4` per factor, `Γℂ` at `π|t|/2`). -/
theorem norm_gammaFactor_le {σ t : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖gammaFactor K ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (Real.sqrt (12*π))^(nrRealPlaces K) * (8 * Real.sqrt (12*π))^(nrComplexPlaces K)
        * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K)
        * Real.exp (-(((nrRealPlaces K + 2 * nrComplexPlaces K : ℕ) : ℝ) * (π * |t|)) / 4)
      := by
  rw [gammaFactor, norm_mul, norm_pow, norm_pow]
  have hE2 : Real.exp (-(π * |t|) / 2) = (Real.exp (-(π * |t|) / 4))^2 := by
    rw [show -(π * |t|) / 2 = -(π * |t|) / 4 + -(π * |t|) / 4 by ring, Real.exp_add, sq]
  have hb1 := norm_Gammaℝ_le (h1 := h1) (h2 := h2) (ht := ht)
  have hb2 := norm_Gammaℂ_le (h1 := h1) (h2 := h2) (ht := ht)
  have hp1 : ‖Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ nrRealPlaces K
      ≤ (Real.sqrt (12*π) * (1 + |t|) * Real.exp (-(π * |t|) / 4)) ^ nrRealPlaces K :=
    pow_le_pow_left₀ (norm_nonneg _) hb1 _
  have hp2 : ‖Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ nrComplexPlaces K
      ≤ (8 * Real.sqrt (12*π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2))
        ^ nrComplexPlaces K :=
    pow_le_pow_left₀ (norm_nonneg _) hb2 _
  refine le_trans (mul_le_mul hp1 hp2 (by positivity) (by positivity)) (le_of_eq ?_)
  rw [hE2]
  rw [show (Real.sqrt (12*π) * (1 + |t|) * Real.exp (-(π * |t|) / 4)) ^ nrRealPlaces K
      * (8 * Real.sqrt (12*π) * (1 + |t|)^2 * (Real.exp (-(π * |t|) / 4))^2)
        ^ nrComplexPlaces K
      = (Real.sqrt (12*π))^(nrRealPlaces K) * (8 * Real.sqrt (12*π))^(nrComplexPlaces K)
        * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K)
        * (Real.exp (-(π * |t|) / 4))^(nrRealPlaces K + 2 * nrComplexPlaces K) by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, pow_add, ← pow_mul, pow_add, ← pow_mul]
    ring]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- On `Re s ≥ 2` the Dedekind zeta function is bounded by its norm-sum at `2`. -/
theorem norm_dedekindZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖dedekindZeta K s‖
      ≤ ∑' n : ℕ, ‖LSeries.term
          (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖ := by
  set f : ℕ → ℂ := fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)
    with hf
  have hsum2 : LSeriesSummable f 2 := by
    have h := count_LSeriesSummable K (by norm_num : (1:ℝ) < 2)
    have hfe : (fun n : ℕ =>
        ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) = f := by
      funext n
      rw [hf]
      push_cast
      rfl
    rw [hfe] at h
    exact_mod_cast h
  have hsummS : LSeriesSummable f s := hsum2.of_re_le_re (by simpa using hs)
  have hterm : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ ‖LSeries.term f 2 n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn0, if_neg hn0,
      show ((2:ℂ)).re = (2:ℝ) by norm_num]
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    gcongr
  calc ‖dedekindZeta K s‖ = ‖∑' n : ℕ, LSeries.term f s n‖ := by rw [dedekindZeta]; rfl
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsummS.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term f 2 n‖ :=
        (hsummS.norm).tsum_le_tsum hterm (hsum2.norm)

/-- **Decaying upper for `H` on the line `Re = 2`** (A3-c): the polynomial factors and
the prefactor are tame, the gamma factor supplies the `e^{-n_K π|t|/4}` envelope, and
the zeta factor is bounded. -/
theorem exists_H_two_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ‖completedDedekindZetaEntire K (((2:ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K + 2)
          * Real.exp (-(((nrRealPlaces K + 2 * nrComplexPlaces K : ℕ) : ℝ) * (π * |t|))
            / 4) := by
  set T₂ : ℝ := ∑' n : ℕ, ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖ with hT₂
  have hT₂0 : 0 ≤ T₂ := tsum_nonneg (fun n => norm_nonneg _)
  refine ⟨6 * (|((discr K : ℤ) : ℝ)| + 2)
    * ((Real.sqrt (12*π))^(nrRealPlaces K) * (8 * Real.sqrt (12*π))^(nrComplexPlaces K))
    * (T₂ + 1), by positivity, fun t ht => ?_⟩
  set s : ℂ := ((2:ℝ) : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = 2 := by simp [hs]
  have hs0 : s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [hsre] at this
    norm_num at this
  have hs1 : s ≠ 1 := by
    intro h0
    have := congrArg Complex.re h0
    rw [hsre] at this
    norm_num at this
  have hs2 : (1:ℝ) < s.re := by rw [hsre]; norm_num
  rw [completedDedekindZetaEntire_eq K hs0 hs1,
    completedDedekindZeta_eq_of_one_lt_re K hs2, completedZetaPrefactor]
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have h1t : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hsn : ‖s‖ ≤ 2 * (1 + |t|) := by
    rw [hs]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, show |(2:ℝ)| = 2 by norm_num]
    linarith [abs_nonneg t]
  have hsn1 : ‖s - 1‖ ≤ 3 * (1 + |t|) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_one]
    linarith [hsn]
  have hdne : ((discr K : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.discr_ne_zero K
  have hdpos : (0:ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.mpr hdne
  have hΔ : ‖((|discr K| : ℝ) : ℂ) ^ (s / 2)‖ ≤ |((discr K : ℤ) : ℝ)| + 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hdpos]
    have hre2 : (s / 2).re = 1 := by
      rw [show s / 2 = ((1:ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I by
        rw [hs]; push_cast; ring]
      simp
    rw [hre2, Real.rpow_one]
    linarith
  have hγ := norm_gammaFactor_le K (σ := 2) (t := t) (by norm_num) (by norm_num) ht
  rw [show (((2:ℝ) : ℂ) + (t : ℂ) * Complex.I) = s from rfl] at hγ
  have hζ : ‖dedekindZeta K s‖ ≤ T₂ + 1 := by
    refine le_trans (norm_dedekindZeta_le_of_two_le_re K (s := s) (by rw [hsre])) ?_
    rw [← hT₂]
    linarith
  calc ‖s‖ * ‖s - 1‖ * (‖((|discr K| : ℝ) : ℂ) ^ (s / 2)‖ * ‖gammaFactor K s‖
        * ‖dedekindZeta K s‖)
      ≤ (2 * (1 + |t|)) * (3 * (1 + |t|)) * ((|((discr K : ℤ) : ℝ)| + 2)
          * ((Real.sqrt (12*π))^(nrRealPlaces K)
              * (8 * Real.sqrt (12*π))^(nrComplexPlaces K)
            * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K)
            * Real.exp (-(((nrRealPlaces K + 2 * nrComplexPlaces K : ℕ) : ℝ)
              * (π * |t|)) / 4))
          * (T₂ + 1)) := by
        gcongr
    _ = 6 * (|((discr K : ℤ) : ℝ)| + 2)
        * ((Real.sqrt (12*π))^(nrRealPlaces K) * (8 * Real.sqrt (12*π))^(nrComplexPlaces K))
        * (T₂ + 1)
        * ((1 + |t|)^2 * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K))
        * Real.exp (-(((nrRealPlaces K + 2 * nrComplexPlaces K : ℕ) : ℝ) * (π * |t|))
          / 4) := by ring
    _ = 6 * (|((discr K : ℤ) : ℝ)| + 2)
        * ((Real.sqrt (12*π))^(nrRealPlaces K) * (8 * Real.sqrt (12*π))^(nrComplexPlaces K))
        * (T₂ + 1)
        * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K + 2)
        * Real.exp (-(((nrRealPlaces K + 2 * nrComplexPlaces K : ℕ) : ℝ) * (π * |t|))
          / 4) := by
        rw [show nrRealPlaces K + 2 * nrComplexPlaces K + 2
            = 2 + (nrRealPlaces K + 2 * nrComplexPlaces K) by ring, pow_add]
        ring

/-- **The functional equation for the entire completed zeta** (A3-d):
`H(1-s) = H(s)`, since `s(s-1)` is symmetric under `s ↦ 1-s` and `Λ_K(1-s) = Λ_K(s)`;
the two exceptional points are absorbed by continuity. -/
theorem completedDedekindZetaEntire_one_sub (s : ℂ) :
    completedDedekindZetaEntire K (1 - s) = completedDedekindZetaEntire K s := by
  have hcont1 : Continuous (fun z : ℂ => completedDedekindZetaEntire K (1 - z)) :=
    ((differentiable_completedDedekindZetaEntire K).comp
      ((differentiable_const (1:ℂ)).sub differentiable_id)).continuous
  have hcont2 : Continuous (completedDedekindZetaEntire K) :=
    (differentiable_completedDedekindZetaEntire K).continuous
  have hdense : Dense ({(0:ℂ), 1}ᶜ : Set ℂ) :=
    Set.Countable.dense_compl ℝ
      ((Set.toFinite ({(0:ℂ), 1} : Set ℂ)).countable)
  refine congrFun (Continuous.ext_on hdense hcont1 hcont2 ?_) s
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
  obtain ⟨hz0, hz1⟩ := hz
  show completedDedekindZetaEntire K (1 - z) = completedDedekindZetaEntire K z
  have h1z0 : (1:ℂ) - z ≠ 0 := by
    intro h0
    apply hz1
    linear_combination -h0
  have h1z1 : (1:ℂ) - z ≠ 1 := by
    intro h0
    apply hz0
    linear_combination -h0
  rw [completedDedekindZetaEntire_eq K h1z0 h1z1, completedDedekindZetaEntire_eq K hz0 hz1,
    completedDedekindZeta_one_sub K z]
  ring

/-- On the strip `-1 ≤ Re z ≤ 2`, the normalizer `z - 4` dominates both the constant 2
and the height: `1 + |Im z| ≤ 2‖z - 4‖`. -/
theorem one_add_abs_im_le_two_norm_sub_four {z : ℂ} (_h1 : -1 ≤ z.re) (h2 : z.re ≤ 2) :
    1 + |z.im| ≤ 2 * ‖z - 4‖ := by
  have hre4 : (z - 4).re = z.re - 4 := by simp
  have hre : (2:ℝ) ≤ ‖z - 4‖ := by
    have habs : (2:ℝ) ≤ |(z - 4).re| := by
      rw [hre4, abs_sub_comm z.re 4, abs_of_pos (by linarith : (0:ℝ) < 4 - z.re)]
      linarith
    exact le_trans habs (Complex.abs_re_le_norm _)
  have him : |z.im| ≤ ‖z - 4‖ := by
    have h : |(z - 4).im| ≤ ‖z - 4‖ := Complex.abs_im_le_norm _
    simpa using h
  linarith

/-- The comparator sine-exponent: `n_K = r₁ + 2r₂`. -/
noncomputable def gammaExponent : ℕ := nrRealPlaces K + 2 * nrComplexPlaces K

/-- Right boundary bound for the comparator
`G = H⁴·sin(πz)^{n_K}/(z-4)^{4n_K+8}` on `Re z = 2`. -/
theorem comparator_bound_right :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ,
      ‖completedDedekindZetaEntire K (((2:ℝ) : ℂ) + (t : ℂ) * Complex.I)‖^4
        * ‖Complex.sin (π * (((2:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖^(gammaExponent K)
        / ‖(((2:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4‖^(4 * gammaExponent K + 8)
      ≤ M := by
  obtain ⟨C, hC0, hC⟩ := exists_H_two_line_bound K
  obtain ⟨B, hB0, hB⟩ :=
    exists_completedDedekindZetaEntire_strip_bound K (-1) 2 (by norm_num)
  set n : ℕ := gammaExponent K with hn
  refine ⟨C^4 * 2^(4*n+8) + (B * 25)^4 * Real.exp ((n:ℝ) * (π * 2)) / 2^(4*n+8),
    by positivity, fun t => ?_⟩
  set z : ℂ := ((2:ℝ) : ℂ) + (t : ℂ) * Complex.I with hz
  have hzre : z.re = 2 := by simp [hz]
  have hzim : z.im = t := by simp [hz]
  have hnorm4 : (1:ℝ) + |t| ≤ 2 * ‖z - 4‖ := by
    have := one_add_abs_im_le_two_norm_sub_four (z := z) (by rw [hzre]; norm_num)
      (by rw [hzre])
    rwa [hzim] at this
  have h2z : (2:ℝ) ≤ ‖z - 4‖ := by
    have habs : (2:ℝ) ≤ |(z - 4).re| := by
      rw [show (z - 4).re = z.re - 4 by simp, hzre]
      norm_num
    exact le_trans habs (Complex.abs_re_le_norm _)
  have hz4pos : (0:ℝ) < ‖z - 4‖ := by linarith
  have hsin : ‖Complex.sin (π * z)‖ ≤ Real.exp (π * |t|) := by
    have := norm_sin_pi_mul_le z
    rwa [hzim] at this
  rcases le_or_gt 2 |t| with ht | ht
  · have hH := hC t ht
    rw [← hz] at hH
    have hHn : ‖completedDedekindZetaEntire K z‖^4
        ≤ C^4 * (1+|t|)^(4*n+8) * Real.exp (-((n:ℝ) * (π * |t|))) := by
      calc ‖completedDedekindZetaEntire K z‖^4
          ≤ (C * (1 + |t|)^(n + 2)
              * Real.exp (-(((n:ℕ) : ℝ) * (π * |t|)) / 4))^4 :=
            pow_le_pow_left₀ (norm_nonneg _) hH 4
        _ = C^4 * (1+|t|)^(4*n+8) * Real.exp (-((n:ℝ) * (π * |t|))) := by
            rw [mul_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul]
            rw [show (n + 2) * 4 = 4*n+8 by ring]
            congr 2
            push_cast
            ring
    have hsinn : ‖Complex.sin (π * z)‖^n ≤ Real.exp ((n:ℝ) * (π * |t|)) := by
      calc ‖Complex.sin (π * z)‖^n ≤ (Real.exp (π * |t|))^n :=
            pow_le_pow_left₀ (norm_nonneg _) hsin n
        _ = Real.exp ((n:ℝ) * (π * |t|)) := by rw [← Real.exp_nat_mul]
    have hnum : ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n
        ≤ C^4 * (1+|t|)^(4*n+8) := by
      calc ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n
          ≤ (C^4 * (1+|t|)^(4*n+8) * Real.exp (-((n:ℝ) * (π * |t|))))
            * Real.exp ((n:ℝ) * (π * |t|)) :=
            mul_le_mul hHn hsinn (by positivity) (by positivity)
        _ = C^4 * (1+|t|)^(4*n+8) * (Real.exp (-((n:ℝ) * (π * |t|)))
            * Real.exp ((n:ℝ) * (π * |t|))) := by ring
        _ = C^4 * (1+|t|)^(4*n+8) := by
            rw [← Real.exp_add]
            norm_num
    calc ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n
        / ‖z - 4‖^(4*n+8)
        ≤ C^4 * (1+|t|)^(4*n+8) / ‖z - 4‖^(4*n+8) := by gcongr
      _ ≤ C^4 * (2 * ‖z - 4‖)^(4*n+8) / ‖z - 4‖^(4*n+8) := by
          gcongr
      _ = C^4 * 2^(4*n+8) := by
          rw [mul_pow, mul_div_assoc, mul_div_assoc,
            div_self (pow_ne_zero _ hz4pos.ne'), mul_one]
      _ ≤ C^4 * 2^(4*n+8)
          + (B * 25)^4 * Real.exp ((n:ℝ) * (π * 2)) / 2^(4*n+8) :=
          le_add_of_nonneg_right (by positivity)
  · have hzn : ‖z‖ ≤ 4 := by
      rw [hz]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, show |(2:ℝ)| = 2 by norm_num]
      linarith
    have hH := hB z (by rw [hzre]; norm_num) (by rw [hzre])
    have hH4 : ‖completedDedekindZetaEntire K z‖^4 ≤ (B*25)^4 := by
      refine pow_le_pow_left₀ (norm_nonneg _) (le_trans hH ?_) 4
      have h25 : (1+‖z‖)^2 ≤ 25 := by nlinarith [norm_nonneg z, hzn]
      nlinarith [hB0]
    have hsinn : ‖Complex.sin (π * z)‖^n ≤ Real.exp ((n:ℝ) * (π * 2)) := by
      calc ‖Complex.sin (π * z)‖^n ≤ (Real.exp (π * |t|))^n :=
            pow_le_pow_left₀ (norm_nonneg _) hsin n
        _ = Real.exp ((n:ℝ) * (π * |t|)) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp ((n:ℝ) * (π * 2)) := by
            rw [Real.exp_le_exp]
            have hπ0 : (0:ℝ) ≤ π := Real.pi_pos.le
            nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hπ0)
              (by linarith [ht.le] : (0:ℝ) ≤ 2 - |t|)]
    have hden : (2:ℝ)^(4*n+8) ≤ ‖z - 4‖^(4*n+8) :=
      pow_le_pow_left₀ (by norm_num) h2z _
    have hnum2 : ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n
        ≤ (B*25)^4 * Real.exp ((n:ℝ) * (π * 2)) :=
      mul_le_mul hH4 hsinn (pow_nonneg (norm_nonneg _) n)
        (pow_nonneg (by positivity) 4)
    calc ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n
        / ‖z - 4‖^(4*n+8)
        ≤ (‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n)
          / 2^(4*n+8) :=
          div_le_div_of_nonneg_left
            (mul_nonneg (pow_nonneg (norm_nonneg _) 4) (pow_nonneg (norm_nonneg _) n))
            (by positivity) hden
      _ ≤ (B*25)^4 * Real.exp ((n:ℝ) * (π * 2)) / 2^(4*n+8) := by
          gcongr
      _ ≤ C^4 * 2^(4*n+8)
          + (B * 25)^4 * Real.exp ((n:ℝ) * (π * 2)) / 2^(4*n+8) :=
          le_add_of_nonneg_left (by positivity)

/-- Left boundary bound for the comparator on `Re z = -1`, by reflecting to the right
boundary through the functional equation. -/
theorem comparator_bound_left :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ,
      ‖completedDedekindZetaEntire K (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)‖^4
        * ‖Complex.sin (π * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖^(gammaExponent K)
        / ‖(((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4‖^(4 * gammaExponent K + 8)
      ≤ M := by
  obtain ⟨M, hM0, hM⟩ := comparator_bound_right K
  refine ⟨M, hM0, fun t => ?_⟩
  set n : ℕ := gammaExponent K with hn
  -- the functional equation sends -1+it to 2-it
  have hH : completedDedekindZetaEntire K (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = completedDedekindZetaEntire K (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by
    have := completedDedekindZetaEntire_one_sub K (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)
    rw [show (1:ℂ) - (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = ((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring] at this
    exact this.symm
  -- the sine moduli agree: both lines have vanishing real sine part
  have hsin : ‖Complex.sin (π * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
      = ‖Complex.sin (π * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖ := by
    have hd1 : (π : ℂ) * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = ((π * (-1) : ℝ) : ℂ) + ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hd2 : (π : ℂ) * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
        = ((π * 2 : ℝ) : ℂ) + ((π * (-t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hsq1 := norm_sin_add_mul_I_sq (π * (-1)) (π * t)
    have hsq2 := norm_sin_add_mul_I_sq (π * 2) (π * (-t))
    rw [← hd1] at hsq1
    rw [← hd2] at hsq2
    have hv1 : Real.sin (π * (-1)) = 0 := by
      rw [show π * (-1) = -π by ring, Real.sin_neg, Real.sin_pi, neg_zero]
    have hv2 : Real.sin (π * 2) = 0 := by
      rw [show π * 2 = 2 * π by ring, Real.sin_two_pi]
    rw [hv1] at hsq1
    rw [hv2] at hsq2
    have hs1 : ‖Complex.sin ((π : ℂ) * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖^2
        = ‖Complex.sin ((π : ℂ) * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖^2 := by
      rw [hsq1, hsq2]
      rw [show π * (-t) = -(π * t) by ring, Real.sinh_neg]
      ring
    calc ‖Complex.sin ((π : ℂ) * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
        = Real.sqrt (‖Complex.sin ((π : ℂ) * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖^2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖Complex.sin ((π : ℂ)
            * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖^2) := by rw [hs1]
      _ = ‖Complex.sin ((π : ℂ) * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖ :=
          Real.sqrt_sq (norm_nonneg _)
  -- the left denominator dominates the right one
  have hden : ‖(((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 4‖
      ≤ ‖(((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4‖ := by
    have he1 : (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 4
        = ((-2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have he2 : (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4
        = ((-5 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he1, he2, Complex.norm_add_mul_I, Complex.norm_add_mul_I]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [sq_nonneg t]
  have hdenpos : (0:ℝ) < ‖(((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 4‖ := by
    have : (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 4 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      norm_num at this
    exact norm_pos_iff.mpr this
  calc ‖completedDedekindZetaEntire K (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)‖^4
      * ‖Complex.sin (π * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖^n
      / ‖(((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4‖^(4*n+8)
      = ‖completedDedekindZetaEntire K (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖^4
        * ‖Complex.sin (π * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖^n
        / ‖(((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4‖^(4*n+8) := by
        rw [hH, hsin]
    _ ≤ ‖completedDedekindZetaEntire K (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖^4
        * ‖Complex.sin (π * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖^n
        / ‖(((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 4‖^(4*n+8) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (pow_nonneg (norm_nonneg _) 4) (pow_nonneg (norm_nonneg _) n))
          (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hden _)
    _ ≤ M := hM (-t)

/-- **The comparator is bounded on the whole strip** `-1 ≤ Re z ≤ 2`
(Phragmén–Lindelöf between the two boundary bounds). -/
theorem comparator_bound_strip :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 →
      ‖completedDedekindZetaEntire K z^4 * Complex.sin (π * z)^(gammaExponent K)
        / (z - 4)^(4 * gammaExponent K + 8)‖ ≤ M := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := comparator_bound_left K
  obtain ⟨M₂, hM₂0, hM₂⟩ := comparator_bound_right K
  obtain ⟨B, hB0, hB⟩ :=
    exists_completedDedekindZetaEntire_strip_bound K (-1) 2 (by norm_num)
  set n : ℕ := gammaExponent K with hn
  set f : ℂ → ℂ := fun z => completedDedekindZetaEntire K z^4
    * Complex.sin (π * z)^n / (z - 4)^(4*n+8) with hf
  refine ⟨M₁ + M₂, by positivity, fun z h1 h2 => ?_⟩
  -- z - 4 is nonvanishing up to Re ≤ 3
  have hne4 : ∀ w : ℂ, w.re ≤ 2 → w - 4 ≠ 0 := by
    intro w hw h0
    have := congrArg Complex.re h0
    simp [sub_eq_zero] at this
    rw [this] at hw
    norm_num at hw
  -- differentiability up to the boundary
  have hfd : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo (-1 : ℝ) 2) := by
    have hcl : closure (Complex.re ⁻¹' Set.Ioo (-1 : ℝ) 2)
        ⊆ Complex.re ⁻¹' Set.Icc (-1 : ℝ) 2 :=
      closure_minimal (fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩)
        (IsClosed.preimage Complex.continuous_re isClosed_Icc)
    refine DifferentiableOn.diffContOnCl ?_
    intro w hw
    have hw2 : w.re ≤ 2 := (hcl hw).2
    exact (((((differentiable_completedDedekindZetaEntire K) w).pow 4).mul
      (((Complex.differentiable_sin.comp
        ((differentiable_const _).mul differentiable_id)).differentiableAt).pow n)).div
      ((differentiable_id.sub_const (4:ℂ)).differentiableAt.pow _)
      (pow_ne_zero _ (hne4 w hw2))).differentiableWithinAt
  -- sub-double-exponential growth
  have hgrow : ∃ c < π / (2 - (-1) : ℝ), ∃ Bg,
      f =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop
          ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo (-1 : ℝ) 2)]
        fun z => Real.exp (Bg * Real.exp (c * |z.im|)) := by
    refine ⟨1, ?_, 8 + (n:ℝ) * π, ?_⟩
    · rw [show (2 - (-1) : ℝ) = 3 by norm_num, lt_div_iff₀ (by norm_num : (0:ℝ) < 3)]
      linarith [Real.pi_gt_three]
    refine Asymptotics.IsBigO.of_bound (B^4 * Real.exp 16) ?_
    rw [Filter.eventually_inf_principal]
    refine Filter.Eventually.of_forall (fun w hw => ?_)
    have hw1 : -1 ≤ w.re := le_of_lt hw.1
    have hw2 : w.re ≤ 2 := le_of_lt hw.2
    have hden2 : (2:ℝ) ≤ ‖w - 4‖ := by
      have habs : (2:ℝ) ≤ |(w - 4).re| := by
        rw [show (w - 4).re = w.re - 4 by simp, abs_sub_comm,
          abs_of_pos (by linarith : (0:ℝ) < 4 - w.re)]
        linarith
      exact le_trans habs (Complex.abs_re_le_norm _)
    have hH := hB w hw1 hw2
    have hwn : ‖w‖ ≤ 2 + |w.im| := by
      calc ‖w‖ = ‖(w.re : ℂ) + (w.im : ℂ) * Complex.I‖ := by rw [Complex.re_add_im]
        _ ≤ ‖(w.re : ℂ)‖ + ‖(w.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |w.re| + |w.im| := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 2 + |w.im| := by
            have : |w.re| ≤ 2 := abs_le.mpr ⟨by linarith, hw2⟩
            linarith
    have hHb : ‖completedDedekindZetaEntire K w‖ ≤ B * (3 + |w.im|)^2 := by
      refine le_trans hH ?_
      have h1w : 1 + ‖w‖ ≤ 3 + |w.im| := by linarith
      have hsq : (1 + ‖w‖)^2 ≤ (3 + |w.im|)^2 := by
        have h0 : (0:ℝ) ≤ 1 + ‖w‖ := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_left hsq hB0
    have hsinw : ‖Complex.sin (π * w)‖ ≤ Real.exp (π * |w.im|) := norm_sin_pi_mul_le w
    -- assemble the crude growth estimate
    have hfw : ‖f w‖ ≤ (B * (3 + |w.im|)^2)^4 * Real.exp ((n:ℝ) * (π * |w.im|)) := by
      rw [hf]
      have hnum : ‖completedDedekindZetaEntire K w^4 * Complex.sin (π * w)^n‖
          ≤ (B * (3 + |w.im|)^2)^4 * Real.exp ((n:ℝ) * (π * |w.im|)) := by
        rw [norm_mul, norm_pow, norm_pow]
        refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hHb 4) ?_
          (pow_nonneg (norm_nonneg _) n) (by positivity)
        calc ‖Complex.sin (π * w)‖^n ≤ (Real.exp (π * |w.im|))^n :=
              pow_le_pow_left₀ (norm_nonneg _) hsinw n
          _ = Real.exp ((n:ℝ) * (π * |w.im|)) := by rw [← Real.exp_nat_mul]
      calc ‖completedDedekindZetaEntire K w^4 * Complex.sin (π * w)^n
            / (w - 4)^(4*n+8)‖
          = ‖completedDedekindZetaEntire K w^4 * Complex.sin (π * w)^n‖
            / ‖w - 4‖^(4*n+8) := by rw [norm_div, norm_pow]
        _ ≤ ‖completedDedekindZetaEntire K w^4 * Complex.sin (π * w)^n‖ / 1 := by
            gcongr
            exact one_le_pow₀ (by linarith)
        _ = ‖completedDedekindZetaEntire K w^4 * Complex.sin (π * w)^n‖ := div_one _
        _ ≤ (B * (3 + |w.im|)^2)^4 * Real.exp ((n:ℝ) * (π * |w.im|)) := hnum
    -- crude ≤ sub-double-exponential
    have hpoly : (B * (3 + |w.im|)^2)^4 ≤ B^4 * Real.exp (8 * (2 + |w.im|)) := by
      have h3x : 3 + |w.im| ≤ Real.exp (2 + |w.im|) := by
        linarith [Real.add_one_le_exp (2 + |w.im|)]
      have h3x2 : (3 + |w.im|)^2 ≤ Real.exp (2 * (2 + |w.im|)) := by
        calc (3 + |w.im|)^2 ≤ (Real.exp (2 + |w.im|))^2 :=
              pow_le_pow_left₀ (by positivity) h3x 2
          _ = Real.exp (2 * (2 + |w.im|)) := by
              rw [← Real.exp_nat_mul]
              norm_num
      calc (B * (3 + |w.im|)^2)^4 = B^4 * ((3 + |w.im|)^2)^4 := by ring
        _ ≤ B^4 * (Real.exp (2 * (2 + |w.im|)))^4 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have h0 : (0:ℝ) ≤ (3 + |w.im|)^2 := by positivity
            exact pow_le_pow_left₀ h0 h3x2 4
        _ = B^4 * Real.exp (8 * (2 + |w.im|)) := by
            congr 1
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
    have hfinal : ‖f w‖ ≤ B^4 * Real.exp 16
        * Real.exp ((8 + (n:ℝ) * π) * |w.im|) := by
      refine le_trans hfw ?_
      calc (B * (3 + |w.im|)^2)^4 * Real.exp ((n:ℝ) * (π * |w.im|))
          ≤ (B^4 * Real.exp (8 * (2 + |w.im|))) * Real.exp ((n:ℝ) * (π * |w.im|)) :=
            mul_le_mul_of_nonneg_right hpoly (by positivity)
        _ = B^4 * Real.exp 16 * Real.exp ((8 + (n:ℝ) * π) * |w.im|) := by
            rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
            congr 2
            ring
    refine le_trans hfinal ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexp_le : Real.exp ((8 + (n:ℝ) * π) * |w.im|)
        ≤ Real.exp ((8 + (n:ℝ) * π) * Real.exp (1 * |w.im|)) := by
      rw [Real.exp_le_exp, one_mul]
      have hc0 : (0:ℝ) ≤ 8 + (n:ℝ) * π := by positivity
      have himle : |w.im| ≤ Real.exp |w.im| := by
        linarith [Real.add_one_le_exp |w.im|]
      nlinarith
    exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
  -- boundary bounds in PL form
  have hle_a : ∀ w : ℂ, w.re = -1 → ‖f w‖ ≤ M₁ + M₂ := by
    intro w hw
    have hweq : w = ((-1:ℝ) : ℂ) + (w.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hw]
    have := hM₁ w.im
    rw [← hweq] at this
    rw [hf]
    calc ‖completedDedekindZetaEntire K w^4 * Complex.sin (π * w)^(gammaExponent K)
          / (w - 4)^(4 * gammaExponent K + 8)‖
        = ‖completedDedekindZetaEntire K w‖^4
          * ‖Complex.sin (π * w)‖^(gammaExponent K)
          / ‖w - 4‖^(4 * gammaExponent K + 8) := by
          rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow]
      _ ≤ M₁ := this
      _ ≤ M₁ + M₂ := by linarith
  have hle_b : ∀ w : ℂ, w.re = 2 → ‖f w‖ ≤ M₁ + M₂ := by
    intro w hw
    have hweq : w = ((2:ℝ) : ℂ) + (w.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hw]
    have := hM₂ w.im
    rw [← hweq] at this
    rw [hf]
    calc ‖completedDedekindZetaEntire K w^4 * Complex.sin (π * w)^(gammaExponent K)
          / (w - 4)^(4 * gammaExponent K + 8)‖
        = ‖completedDedekindZetaEntire K w‖^4
          * ‖Complex.sin (π * w)‖^(gammaExponent K)
          / ‖w - 4‖^(4 * gammaExponent K + 8) := by
          rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow]
      _ ≤ M₂ := this
      _ ≤ M₁ + M₂ := by linarith
  show ‖f z‖ ≤ M₁ + M₂
  exact PhragmenLindelof.vertical_strip hfd hgrow hle_a hle_b h1 h2

/-- **AC-A3 deliverable: the envelope-matched decaying upper bound for `H` on the
critical strip.** For `-1 ≤ Re z ≤ 2` and `|Im z| ≥ 1`,
`‖H(z)‖ ≤ C·(1+|Im z|)^{n_K+2}·e^{-n_K·π|Im z|/4}` — the same exponential rate as the
center lower bounds, so Jensen ratios are polynomial. -/
theorem exists_H_strip_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 1 ≤ |z.im| →
      ‖completedDedekindZetaEntire K z‖
        ≤ C * (1 + |z.im|)^(gammaExponent K + 2)
          * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |z.im|)) / 4) := by
  obtain ⟨M, hM0, hM⟩ := comparator_bound_strip K
  set n : ℕ := gammaExponent K with hn
  refine ⟨(M * 5^(4*n+8) * 3^n) ^ ((1:ℝ)/4) + 1, by positivity, fun z h1 h2 ht => ?_⟩
  set t : ℝ := z.im with hts
  set C₀ : ℝ := (M * 5^(4*n+8) * 3^n) ^ ((1:ℝ)/4) + 1 with hC₀
  have hC₀0 : 0 < C₀ := by positivity
  -- the comparator bound, cleared of the normalizer
  have hcomp := hM z h1 h2
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow] at hcomp
  -- sine lower bound
  have hsinlow : Real.exp (π * |t|) / 3 ≤ ‖Complex.sin (π * z)‖ := by
    have hdecomp : (π : ℂ) * z
        = ((π * z.re : ℝ) : ℂ) + ((π * t : ℝ) : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im z]
      push_cast
      ring
    have hsq := norm_sin_add_mul_I_sq (π * z.re) (π * t)
    rw [← hdecomp] at hsq
    have hsinh_abs : Real.sinh (π * |t|) = |Real.sinh (π * t)| := by
      rw [show π * |t| = |π * t| by rw [abs_mul, abs_of_pos Real.pi_pos], ← Real.abs_sinh]
    have hlow : Real.sinh (π * |t|) ≤ ‖Complex.sin (π * z)‖ := by
      rw [hsinh_abs]
      have hsq' : |Real.sinh (π * t)|^2 ≤ ‖Complex.sin (π * z)‖^2 := by
        rw [hsq, sq_abs]
        nlinarith [sq_nonneg (Real.sin (π * z.re))]
      nlinarith [abs_nonneg (Real.sinh (π * t)), norm_nonneg (Complex.sin (π * z))]
    refine le_trans ?_ hlow
    rw [Real.sinh_eq]
    have hx : (3 : ℝ) ≤ Real.exp (π * |t|) := by
      have h4 : (4 : ℝ) ≤ 1 + π * |t| := by nlinarith [Real.pi_gt_three]
      linarith [Real.add_one_le_exp (π * |t|)]
    have hinv : Real.exp (-(π * |t|)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0:ℝ) ≤ π * |t| := by positivity
      linarith
    nlinarith [Real.exp_pos (π * |t|)]
  -- normalizer upper bound
  have hz4up : ‖z - 4‖ ≤ 5 * (1 + |t|) := by
    calc ‖z - 4‖ = ‖((z.re - 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ := by
          congr 1
          conv_lhs => rw [← Complex.re_add_im z]
          push_cast
          ring
      _ ≤ ‖((z.re - 4 : ℝ) : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |z.re - 4| + |t| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 5 * (1 + |t|) := by
          have habs : |z.re - 4| ≤ 5 := by
            rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < 4 - z.re)]
            linarith
          nlinarith [abs_nonneg t]
  -- solve the comparator inequality for ‖H‖⁴
  have hsinpos : (0:ℝ) < ‖Complex.sin (π * z)‖ := by
    have h3 : (0:ℝ) < Real.exp (π * |t|) / 3 := by positivity
    linarith
  have hH4 : ‖completedDedekindZetaEntire K z‖^4
      ≤ M * (5 * (1 + |t|))^(4*n+8) * (3 * Real.exp (-(π * |t|))) ^ n := by
    have hpos : (0:ℝ) < ‖z - 4‖^(4*n+8) := by
      have h2z : (0:ℝ) < ‖z - 4‖ := by
        have habs : (2:ℝ) ≤ |(z - 4).re| := by
          rw [show (z - 4).re = z.re - 4 by simp, abs_sub_comm,
            abs_of_pos (by linarith : (0:ℝ) < 4 - z.re)]
          linarith
        linarith [le_trans habs (Complex.abs_re_le_norm (z - 4))]
      positivity
    have hstep : ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n
        ≤ M * ‖z - 4‖^(4*n+8) := by
      rw [div_le_iff₀ hpos] at hcomp
      exact hcomp
    have hsinn : (Real.exp (π * |t|) / 3)^n ≤ ‖Complex.sin (π * z)‖^n :=
      pow_le_pow_left₀ (by positivity) hsinlow n
    have hkey : ‖completedDedekindZetaEntire K z‖^4 * (Real.exp (π * |t|) / 3)^n
        ≤ M * (5 * (1 + |t|))^(4*n+8) := by
      calc ‖completedDedekindZetaEntire K z‖^4 * (Real.exp (π * |t|) / 3)^n
          ≤ ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n :=
            mul_le_mul_of_nonneg_left hsinn (by positivity)
        _ ≤ M * ‖z - 4‖^(4*n+8) := hstep
        _ ≤ M * (5 * (1 + |t|))^(4*n+8) := by
            refine mul_le_mul_of_nonneg_left ?_ hM0.le
            exact pow_le_pow_left₀ (norm_nonneg _) hz4up _
    have hEinv : ((Real.exp (π * |t|) / 3)^n)⁻¹ = (3 * Real.exp (-(π * |t|)))^n := by
      rw [← inv_pow]
      congr 1
      rw [Real.exp_neg]
      field_simp
    calc ‖completedDedekindZetaEntire K z‖^4
        = ‖completedDedekindZetaEntire K z‖^4 * (Real.exp (π * |t|) / 3)^n
          * ((Real.exp (π * |t|) / 3)^n)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
      _ ≤ M * (5 * (1 + |t|))^(4*n+8) * ((Real.exp (π * |t|) / 3)^n)⁻¹ :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = M * (5 * (1 + |t|))^(4*n+8) * (3 * Real.exp (-(π * |t|))) ^ n := by
          rw [hEinv]
  have hC₀4 : M * 5^(4*n+8) * 3^n ≤ C₀^4 := by
    have hpow : ((M * 5^(4*n+8) * 3^n) ^ ((1:ℝ)/4))^(4:ℕ) = M * 5^(4*n+8) * 3^n := by
      rw [← Real.rpow_natCast ((M * 5^(4*n+8) * 3^n) ^ ((1:ℝ)/4)) 4,
        ← Real.rpow_mul (by positivity)]
      norm_num
    calc M * 5^(4*n+8) * 3^n = ((M * 5^(4*n+8) * 3^n) ^ ((1:ℝ)/4))^(4:ℕ) := hpow.symm
      _ ≤ C₀^4 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 4
          rw [hC₀]
          linarith
  refine le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ) ≠ 0) (by positivity) ?_
  have hRHS : (C₀ * (1 + |t|)^(n+2)
      * Real.exp (-(((n:ℕ) : ℝ) * (π * |t|)) / 4))^4
      = C₀^4 * (1 + |t|)^(4*n+8) * Real.exp (-((n:ℝ) * (π * |t|))) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul]
    rw [show (n+2)*4 = 4*n+8 by ring]
    congr 2
    push_cast
    ring
  rw [hRHS]
  refine le_trans hH4 ?_
  have hLHS : M * (5 * (1 + |t|))^(4*n+8) * (3 * Real.exp (-(π * |t|))) ^ n
      = (M * 5^(4*n+8) * 3^n) * (1 + |t|)^(4*n+8)
        * Real.exp (-((n:ℝ) * (π * |t|))) := by
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
    rw [show ((n:ℝ)) * -(π * |t|) = -((n:ℝ) * (π * |t|)) by ring]
    ring
  rw [hLHS]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₀4 (by positivity))
    (by positivity)

/-- Rightward propagation of the decaying Γ-upper bound: each recurrence step costs a
factor `‖z‖ + n`, keeping the bound polynomial-times-decaying. -/
theorem norm_Gamma_le_mul_exp_add_nat {σ t : ℝ} (h1 : 1/2 ≤ σ) (h2 : σ ≤ 3/2)
    (ht : 1 ≤ |t|) (n : ℕ) :
    ‖Complex.Gamma (((σ + n : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + n)^n
        * (Real.sqrt (12 * π) * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖
          * Real.exp (-(π * |t|) / 2)) := by
  induction n with
  | zero =>
      have h0 : ((σ + (0:ℕ) : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
      rw [h0]
      simpa using norm_Gamma_le_mul_exp h1 h2 ht
  | succ n ih =>
      have hzim : ((((σ + n : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
      have hzne : (((σ + n : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
        intro h0
        have := congrArg Complex.im h0
        rw [hzim] at this
        simp at this
        rw [this] at ht
        norm_num at ht
      have hstep : ((σ + (n+1:ℕ) : ℝ) : ℂ) + (t : ℂ) * Complex.I
          = ((((σ + n : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + 1 := by
        push_cast
        ring
      rw [hstep, Complex.Gamma_add_one _ hzne, norm_mul]
      have hfacle : ‖(((σ + n : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + n := by
        have hsplit : (((σ + n : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            = ((σ : ℂ) + (t : ℂ) * Complex.I) + (n : ℂ) := by
          push_cast
          ring
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        rw [Complex.norm_natCast]
      have hbase_nonneg : (0:ℝ) ≤ Real.sqrt (12 * π) * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖
          * Real.exp (-(π * |t|) / 2) := by positivity
      have hXn : (0:ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + n := by positivity
      calc ‖(((σ + n : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          * ‖Complex.Gamma (((σ + n : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + n)
            * ((‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + n)^n
              * (Real.sqrt (12 * π) * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖
                * Real.exp (-(π * |t|) / 2))) :=
            mul_le_mul hfacle ih (norm_nonneg _) hXn
        _ = (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + n)^(n+1)
            * (Real.sqrt (12 * π) * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖
              * Real.exp (-(π * |t|) / 2)) := by
            rw [pow_succ]
            ring
        _ ≤ (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + (n+1:ℕ))^(n+1)
            * (Real.sqrt (12 * π) * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖
              * Real.exp (-(π * |t|) / 2)) := by
            refine mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ hXn ?_ _) hbase_nonneg
            push_cast
            linarith

/-- Every real `σ ≥ 1/2` decomposes as a base-strip point plus a natural number:
`σ = σ₀ + n` with `σ₀ ∈ [1/2, 3/2)`. -/
theorem exists_base_add_nat {σ : ℝ} (h : 1/2 ≤ σ) :
    ∃ σ₀ : ℝ, ∃ n : ℕ, 1/2 ≤ σ₀ ∧ σ₀ < 3/2 ∧ σ = σ₀ + n := by
  refine ⟨σ - ⌊σ - 1/2⌋₊, ⌊σ - 1/2⌋₊, ?_, ?_, by ring⟩
  · have hfle : (⌊σ - 1/2⌋₊ : ℝ) ≤ σ - 1/2 := Nat.floor_le (by linarith)
    linarith
  · have hflt : σ - 1/2 < ⌊σ - 1/2⌋₊ + 1 := Nat.lt_floor_add_one _
    linarith

/-- Packaged decaying Γ-upper at an arbitrary abscissa `σ ≥ 1/2`. -/
theorem exists_norm_Gamma_le (σ : ℝ) (hσ : 1/2 ≤ σ) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ, ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|)^P * Real.exp (-(π * |t|) / 2) := by
  obtain ⟨σ₀, n, h1, h2, hdec⟩ := exists_base_add_nat hσ
  refine ⟨(3/2 + n)^n * (Real.sqrt (12 * π) * (3/2)), by positivity, n + 1,
    fun t ht => ?_⟩
  have hb := norm_Gamma_le_mul_exp_add_nat (σ := σ₀) (t := t) h1 (le_of_lt h2) ht n
  rw [← hdec] at hb
  refine le_trans hb ?_
  have hz₀ : ‖(σ₀ : ℂ) + (t : ℂ) * Complex.I‖ ≤ (3/2) * (1 + |t|) :=
    (norm_ofReal_add_mul_I_le σ₀ t (by linarith)).trans (by nlinarith [abs_nonneg t])
  have h1t : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hfac : (‖(σ₀ : ℂ) + (t : ℂ) * Complex.I‖ + n)^n
      ≤ ((3/2 + n) * (1 + |t|))^n := by
    refine pow_le_pow_left₀ (by positivity) ?_ n
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc (‖(σ₀ : ℂ) + (t : ℂ) * Complex.I‖ + n)^n
      * (Real.sqrt (12 * π) * ‖(σ₀ : ℂ) + (t : ℂ) * Complex.I‖
        * Real.exp (-(π * |t|) / 2))
      ≤ ((3/2 + n) * (1 + |t|))^n
        * (Real.sqrt (12 * π) * ((3/2) * (1 + |t|)) * Real.exp (-(π * |t|) / 2)) := by
        refine mul_le_mul hfac ?_ (by positivity) (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hz₀ (by positivity)
    _ = ((3/2 + n)^n * (Real.sqrt (12 * π) * (3/2))) * (1 + |t|)^(n + 1)
        * Real.exp (-(π * |t|) / 2) := by
        rw [mul_pow, pow_succ]
        ring

/-- Packaged matching Γ-lower at an arbitrary abscissa `σ ≥ 1/2`. -/
theorem exists_le_norm_Gamma (σ : ℝ) (hσ : 1/2 ≤ σ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ |t| →
      c * Real.exp (-(π * |t|) / 2) / (1 + |t|)
        ≤ ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨σ₀, n, h1, h2, hdec⟩ := exists_base_add_nat hσ
  refine ⟨π / (Real.sqrt (12 * π) * 3), by positivity, fun t ht => ?_⟩
  have hb := le_norm_Gamma_base_add_nat (σ := σ₀) (t := t) h1 (le_of_lt h2) ht n
  rw [← hdec] at hb
  refine le_trans ?_ hb
  have hz₀ : ‖((2 - σ₀ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖ ≤ 3 * (1 + |t|) := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by linarith : (0:ℝ) < 2 - σ₀)]
    nlinarith [abs_nonneg t]
  have hz₀pos : (0:ℝ) < ‖((2 - σ₀ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖ := by
    have hne : ((2 - σ₀ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      rw [this] at ht
      norm_num at ht
    exact norm_pos_iff.mpr hne
  have hmono : π / (Real.sqrt (12 * π) * 3) / (1 + |t|)
      ≤ π / (Real.sqrt (12 * π)
        * ‖((2 - σ₀ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖) := by
    rw [div_div]
    refine div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) ?_
    calc Real.sqrt (12 * π) * ‖((2 - σ₀ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖
        ≤ Real.sqrt (12 * π) * (3 * (1 + |t|)) :=
          mul_le_mul_of_nonneg_left hz₀ (by positivity)
      _ = Real.sqrt (12 * π) * 3 * (1 + |t|) := by ring
  calc π / (Real.sqrt (12 * π) * 3) * Real.exp (-(π * |t|) / 2) / (1 + |t|)
      = (π / (Real.sqrt (12 * π) * 3) / (1 + |t|)) * Real.exp (-(π * |t|) / 2) := by
        ring
    _ ≤ (π / (Real.sqrt (12 * π)
        * ‖((2 - σ₀ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖))
        * Real.exp (-(π * |t|) / 2) :=
        mul_le_mul_of_nonneg_right hmono (by positivity)

/-- Matching lower bound for `Γℝ` at a fixed abscissa `σ ≥ 1`: rate `e^{-π|t|/4}`. -/
theorem exists_le_norm_Gammaℝ (σ : ℝ) (hσ : 1 ≤ σ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ |t| →
      c * Real.exp (-(π * |t|) / 4) / (1 + |t|)
        ≤ ‖Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨c₀, hc₀, hlow⟩ := exists_le_norm_Gamma (σ/2) (by linarith)
  refine ⟨Real.pi ^ (-σ/2 : ℝ) * c₀, by positivity, fun t ht => ?_⟩
  rw [Complex.Gammaℝ_def, norm_mul]
  have hπnorm : ‖(π : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖
      = Real.pi ^ (-σ/2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    rw [show -((σ : ℂ) + (t : ℂ) * Complex.I) / 2
        = ((-σ/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    simp
  have harg : ((σ : ℂ) + (t : ℂ) * Complex.I) / 2
      = ((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have ht2 : 1 ≤ |t/2| := by
    rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
    linarith
  have hΓ := hlow (t/2) ht2
  rw [hπnorm, harg]
  rw [exp_neg_pi_abs_half_div_two t] at hΓ
  have hmono : c₀ * Real.exp (-(π * |t|) / 4) / (1 + |t|)
      ≤ c₀ * Real.exp (-(π * |t|) / 4) / (1 + |t/2|) := by
    refine div_le_div_of_nonneg_left (by positivity) ?_ ?_
    · have : (0:ℝ) ≤ |t/2| := abs_nonneg _
      linarith
    · rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
      linarith [abs_nonneg t]
  calc Real.pi ^ (-σ/2 : ℝ) * c₀ * Real.exp (-(π * |t|) / 4) / (1 + |t|)
      = Real.pi ^ (-σ/2 : ℝ) * (c₀ * Real.exp (-(π * |t|) / 4) / (1 + |t|)) := by ring
    _ ≤ Real.pi ^ (-σ/2 : ℝ) * (c₀ * Real.exp (-(π * |t|) / 4) / (1 + |t/2|)) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ Real.pi ^ (-σ/2 : ℝ)
        * ‖Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I)‖ :=
        mul_le_mul_of_nonneg_left hΓ (by positivity)

/-- Matching lower bound for `Γℂ` at a fixed abscissa `σ ≥ 1`: rate `e^{-π|t|/2}`. -/
theorem exists_le_norm_Gammaℂ (σ : ℝ) (hσ : 1 ≤ σ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ |t| →
      c * Real.exp (-(π * |t|) / 2) / (1 + |t|)
        ≤ ‖Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨c₀, hc₀, hlow⟩ := exists_le_norm_Gamma σ (by linarith)
  refine ⟨2 * (2*π) ^ (-σ : ℝ) * c₀, by positivity, fun t ht => ?_⟩
  rw [Complex.Gammaℂ_def, norm_mul, norm_mul]
  have h2π : ‖((2:ℂ) * π) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      = (2*π) ^ (-σ : ℝ) := by
    rw [show ((2:ℂ) * π) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1
    simp
  have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
  have hΓ := hlow t (by linarith)
  rw [h2π, h2n]
  calc 2 * (2*π) ^ (-σ : ℝ) * c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)
      = 2 * (2*π) ^ (-σ : ℝ) * (c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)) := by ring
    _ ≤ 2 * (2*π) ^ (-σ : ℝ)
        * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
        mul_le_mul_of_nonneg_left hΓ (by positivity)
    _ = 2 * (2*π) ^ (-σ : ℝ)
        * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by ring

/-- Matching lower bound for the archimedean factor at a fixed abscissa `σ ≥ 1`:
`‖γ_K(σ+it)‖ ≥ c·e^{-n_Kπ|t|/4}/(1+|t|)^{r₁+r₂}` — the same envelope rate as the
upper bound `norm_gammaFactor_le`. -/
theorem exists_gammaFactor_lower (σ : ℝ) (hσ : 1 ≤ σ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ |t| →
      c * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |t|)) / 4)
        / (1 + |t|)^(nrRealPlaces K + nrComplexPlaces K)
        ≤ ‖gammaFactor K ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨c₁, hc₁, hR⟩ := exists_le_norm_Gammaℝ σ hσ
  obtain ⟨c₂, hc₂, hC⟩ := exists_le_norm_Gammaℂ σ hσ
  refine ⟨c₁^(nrRealPlaces K) * c₂^(nrComplexPlaces K), by positivity, fun t ht => ?_⟩
  rw [gammaFactor, norm_mul, norm_pow, norm_pow]
  have hp1 : (c₁ * Real.exp (-(π * |t|) / 4) / (1 + |t|))^(nrRealPlaces K)
      ≤ ‖Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * Complex.I)‖^(nrRealPlaces K) :=
    pow_le_pow_left₀ (by positivity) (hR t ht) _
  have hp2 : (c₂ * Real.exp (-(π * |t|) / 2) / (1 + |t|))^(nrComplexPlaces K)
      ≤ ‖Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I)‖^(nrComplexPlaces K) :=
    pow_le_pow_left₀ (by positivity) (hC t ht) _
  refine le_trans (le_of_eq ?_) (mul_le_mul hp1 hp2 (by positivity) (by positivity))
  -- collect the exponentials and powers
  have hE : Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |t|)) / 4)
      = (Real.exp (-(π * |t|) / 4))^(nrRealPlaces K)
        * (Real.exp (-(π * |t|) / 2))^(nrComplexPlaces K) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [gammaExponent]
    push_cast
    ring
  rw [hE]
  rw [div_pow, div_pow, mul_pow, mul_pow]
  rw [show (1 + |t|)^(nrRealPlaces K + nrComplexPlaces K)
      = (1 + |t|)^(nrRealPlaces K) * (1 + |t|)^(nrComplexPlaces K) from pow_add _ _ _]
  field_simp

/-- **A4 center lower bound**: at the abscissa `A` where `‖ζ_K‖ ≥ 1/2`, the entire
completed zeta obeys the envelope-matched lower
`‖H(A+it)‖ ≥ c·e^{-n_Kπ|t|/4}/(1+|t|)^{r₁+r₂}` for `|t| ≥ 2`. -/
theorem exists_H_center_lower :
    ∃ A : ℝ, 2 ≤ A ∧ ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ |t| →
      c * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |t|)) / 4)
        / (1 + |t|)^(nrRealPlaces K + nrComplexPlaces K)
        ≤ ‖completedDedekindZetaEntire K ((A : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨A, hA2, hζ⟩ := exists_re_norm_dedekindZeta_ge_half K
  obtain ⟨cγ, hcγ, hγ⟩ := exists_gammaFactor_lower K A (by linarith)
  refine ⟨A, hA2, cγ/2, by positivity, fun t ht => ?_⟩
  set s : ℂ := (A : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = A := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have htne : t ≠ 0 := by
    intro h0
    rw [h0] at ht
    norm_num at ht
  have hs0 : s ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    rw [hsim] at this
    simp at this
    exact htne this
  have hs1 : s ≠ 1 := by
    intro h0
    have := congrArg Complex.im h0
    rw [hsim] at this
    simp at this
    exact htne this
  have hsre1 : (1:ℝ) < s.re := by rw [hsre]; linarith
  rw [completedDedekindZetaEntire_eq K hs0 hs1,
    completedDedekindZeta_eq_of_one_lt_re K hsre1, completedZetaPrefactor]
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  -- individual lower bounds
  have hsn : (1:ℝ) ≤ ‖s‖ := by
    calc (1:ℝ) ≤ |t| := by linarith
      _ = |s.im| := by rw [hsim]
      _ ≤ ‖s‖ := Complex.abs_im_le_norm _
  have hsn1 : (1:ℝ) ≤ ‖s - 1‖ := by
    calc (1:ℝ) ≤ |t| := by linarith
      _ = |(s - 1).im| := by rw [show (s-1).im = s.im by simp, hsim]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hΔ : (1:ℝ) ≤ ‖((|discr K| : ℝ) : ℂ) ^ (s / 2)‖ := by
    have hdne : ((discr K : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast NumberField.discr_ne_zero K
    have hd1 : (1:ℝ) ≤ |((discr K : ℤ) : ℝ)| := by
      have := Int.one_le_abs (NumberField.discr_ne_zero K)
      calc (1:ℝ) = ((1:ℤ) : ℝ) := by norm_num
        _ ≤ ((|discr K| : ℤ) : ℝ) := by exact_mod_cast this
        _ = |((discr K : ℤ) : ℝ)| := by push_cast; rfl
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    have hre2 : (s / 2).re = A/2 := by
      rw [show s / 2 = ((A/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I by
        rw [hs]; push_cast; ring]
      simp
    rw [hre2]
    calc (1:ℝ) = |((discr K : ℤ) : ℝ)| ^ (0:ℝ) := by rw [Real.rpow_zero]
      _ ≤ |((discr K : ℤ) : ℝ)| ^ (A/2) :=
          Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  have hγb := hγ t ht
  rw [← hs] at hγb
  have hζb : (1:ℝ)/2 ≤ ‖dedekindZeta K s‖ := hζ s (by rw [hsre])
  -- assemble
  calc cγ/2 * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |t|)) / 4)
      / (1 + |t|)^(nrRealPlaces K + nrComplexPlaces K)
      = 1 * 1 * (1 * (cγ * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |t|)) / 4)
        / (1 + |t|)^(nrRealPlaces K + nrComplexPlaces K)) * (1/2)) := by ring
    _ ≤ ‖s‖ * ‖s - 1‖ * (‖((|discr K| : ℝ) : ℂ) ^ (s / 2)‖
        * ‖gammaFactor K s‖ * ‖dedekindZeta K s‖) := by
        refine mul_le_mul (mul_le_mul hsn hsn1 (by norm_num) (by linarith)) ?_
          (by positivity) (by positivity)
        refine mul_le_mul (mul_le_mul hΔ hγb (by positivity) (by linarith)) hζb
          (by norm_num) ?_
        positivity

/-- σ-uniform decaying Γ-upper on `1/2 ≤ σ ≤ σ₁`, `|t| ≥ 1`. -/
theorem exists_norm_Gamma_le_range (σ₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ, ∀ σ t : ℝ, 1/2 ≤ σ → σ ≤ σ₁ → 1 ≤ |t| →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|)^P * Real.exp (-(π * |t|) / 2) := by
  set N : ℕ := ⌈σ₁⌉₊ with hN
  refine ⟨(3/2 + N)^N * (Real.sqrt (12 * π) * (3/2)), by positivity, N + 1,
    fun σ t hσl hσr ht => ?_⟩
  obtain ⟨σ₀, n, h1, h2, hdec⟩ := exists_base_add_nat hσl
  have hnN : n ≤ N := by
    have hnle : (n : ℝ) ≤ σ := by
      rw [hdec]
      linarith
    have : (n : ℝ) ≤ σ₁ := le_trans hnle hσr
    calc n ≤ ⌈(n : ℝ)⌉₊ := by rw [Nat.ceil_natCast]
      _ ≤ N := Nat.ceil_le_ceil this
  have hb := norm_Gamma_le_mul_exp_add_nat (σ := σ₀) (t := t) h1 (le_of_lt h2) ht n
  rw [← hdec] at hb
  refine le_trans hb ?_
  have h1t : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hz₀ : ‖(σ₀ : ℂ) + (t : ℂ) * Complex.I‖ ≤ (3/2) * (1 + |t|) :=
    (norm_ofReal_add_mul_I_le σ₀ t (by linarith)).trans (by nlinarith [abs_nonneg t])
  have hfac : (‖(σ₀ : ℂ) + (t : ℂ) * Complex.I‖ + n)^n
      ≤ ((3/2 + N) * (1 + |t|))^n := by
    refine pow_le_pow_left₀ (by positivity) ?_ n
    have hnn : (n:ℝ) ≤ N := by exact_mod_cast hnN
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc (‖(σ₀ : ℂ) + (t : ℂ) * Complex.I‖ + n)^n
      * (Real.sqrt (12 * π) * ‖(σ₀ : ℂ) + (t : ℂ) * Complex.I‖
        * Real.exp (-(π * |t|) / 2))
      ≤ ((3/2 + N) * (1 + |t|))^n
        * (Real.sqrt (12 * π) * ((3/2) * (1 + |t|)) * Real.exp (-(π * |t|) / 2)) := by
        refine mul_le_mul hfac ?_ (by positivity) (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hz₀ (by positivity)
    _ = ((3/2 + N)^n * (1 + |t|)^(n+1)) * (Real.sqrt (12 * π) * (3/2))
        * Real.exp (-(π * |t|) / 2) := by
        rw [mul_pow, pow_succ]
        ring
    _ ≤ ((3/2 + N)^N * (1 + |t|)^(N+1)) * (Real.sqrt (12 * π) * (3/2))
        * Real.exp (-(π * |t|) / 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul ?_ ?_ (by positivity) (by positivity)) (by positivity))
          (by positivity)
        · refine pow_le_pow_right₀ ?_ hnN
          have : (0:ℝ) ≤ N := Nat.cast_nonneg N
          linarith
        · exact pow_le_pow_right₀ h1t (by omega)
    _ = (3/2 + N)^N * (Real.sqrt (12 * π) * (3/2)) * (1 + |t|)^(N+1)
        * Real.exp (-(π * |t|) / 2) := by ring

/-- σ-uniform decaying upper for the archimedean factor on `1 ≤ σ ≤ σ₁`, `|t| ≥ 2`. -/
theorem exists_norm_gammaFactor_le_range (σ₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ, ∀ σ t : ℝ, 1 ≤ σ → σ ≤ σ₁ → 2 ≤ |t| →
      ‖gammaFactor K ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|)^P
          * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |t|)) / 4) := by
  obtain ⟨C₀, hC₀, P₀, hΓ⟩ := exists_norm_Gamma_le_range (σ₁/2)
  obtain ⟨C₁, hC₁, P₁, hΓ'⟩ := exists_norm_Gamma_le_range σ₁
  refine ⟨C₀^(nrRealPlaces K) * (2*C₁)^(nrComplexPlaces K), by positivity,
    P₀ * nrRealPlaces K + P₁ * nrComplexPlaces K, fun σ t hσl hσr ht => ?_⟩
  rw [gammaFactor, norm_mul, norm_pow, norm_pow]
  have ht1 : 1 ≤ |t| := by linarith
  -- Γℝ-factor bound
  have hGR : ‖Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ C₀ * (1 + |t|)^P₀ * Real.exp (-(π * |t|) / 4) := by
    rw [Complex.Gammaℝ_def, norm_mul]
    have hπ : ‖(π : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      have hre : (-((σ : ℂ) + (t : ℂ) * Complex.I) / 2).re = -σ/2 := by
        rw [show -((σ : ℂ) + (t : ℂ) * Complex.I) / 2
            = ((-σ/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
        simp
      rw [hre]
      calc π ^ (-σ/2 : ℝ) ≤ π ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
              (by linarith)
        _ = 1 := Real.rpow_zero π
    have harg : ((σ : ℂ) + (t : ℂ) * Complex.I) / 2
        = ((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have ht2 : 1 ≤ |t/2| := by
      rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
      linarith
    have hb := hΓ (σ/2) (t/2) (by linarith) (by linarith) ht2
    rw [harg]
    have hmono : C₀ * (1 + |t/2|)^P₀ * Real.exp (-(π * |t/2|) / 2)
        ≤ C₀ * (1 + |t|)^P₀ * Real.exp (-(π * |t|) / 4) := by
      rw [exp_neg_pi_abs_half_div_two t]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) ?_ _) hC₀.le) (by positivity)
      rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
      linarith [abs_nonneg t]
    calc ‖(π : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖
        * ‖Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I)‖
        ≤ 1 * (C₀ * (1 + |t/2|)^P₀ * Real.exp (-(π * |t/2|) / 2)) :=
          mul_le_mul hπ hb (norm_nonneg _) (by norm_num)
      _ = C₀ * (1 + |t/2|)^P₀ * Real.exp (-(π * |t/2|) / 2) := by ring
      _ ≤ C₀ * (1 + |t|)^P₀ * Real.exp (-(π * |t|) / 4) := hmono
  -- Γℂ-factor bound
  have hGC : ‖Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2 * (C₁ * (1 + |t|)^P₁ * Real.exp (-(π * |t|) / 2)) := by
    rw [Complex.Gammaℂ_def, norm_mul, norm_mul]
    have h2π : ‖((2:ℂ) * π) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1 := by
      rw [show ((2:ℂ) * π) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      have hre : (-((σ : ℂ) + (t : ℂ) * Complex.I)).re = -σ := by simp
      rw [hre]
      calc (2*π) ^ (-σ : ℝ) ≤ (2*π) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
              (by linarith)
        _ = 1 := Real.rpow_zero _
    have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
    have hb := hΓ' σ t (by linarith) hσr ht1
    rw [h2n]
    calc 2 * ‖((2:ℂ) * π) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
        * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ 2 * 1 * (C₁ * (1 + |t|)^P₁ * Real.exp (-(π * |t|) / 2)) := by
          refine mul_le_mul (by nlinarith [norm_nonneg (((2:ℂ) * π)
            ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))]) hb (norm_nonneg _) (by norm_num)
      _ = 2 * (C₁ * (1 + |t|)^P₁ * Real.exp (-(π * |t|) / 2)) := by ring
  -- combine (mirroring norm_gammaFactor_le)
  have hp1 := pow_le_pow_left₀ (norm_nonneg _) hGR (nrRealPlaces K)
  have hp2 := pow_le_pow_left₀ (norm_nonneg _) hGC (nrComplexPlaces K)
  refine le_trans (mul_le_mul hp1 hp2 (by positivity) (by positivity)) (le_of_eq ?_)
  have hE2 : Real.exp (-(π * |t|) / 2) = (Real.exp (-(π * |t|) / 4))^2 := by
    rw [show -(π * |t|) / 2 = -(π * |t|) / 4 + -(π * |t|) / 4 by ring, Real.exp_add, sq]
  rw [hE2]
  rw [show (C₀ * (1 + |t|)^P₀ * Real.exp (-(π*|t|)/4))^(nrRealPlaces K)
      * (2 * (C₁ * (1 + |t|)^P₁ * (Real.exp (-(π*|t|)/4))^2))^(nrComplexPlaces K)
      = C₀^(nrRealPlaces K) * (2*C₁)^(nrComplexPlaces K)
        * (1+|t|)^(P₀ * nrRealPlaces K + P₁ * nrComplexPlaces K)
        * (Real.exp (-(π*|t|)/4))^(nrRealPlaces K + 2 * nrComplexPlaces K) by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
      ← pow_mul, pow_add]
    ring]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  rw [gammaExponent]
  push_cast
  ring

/-- Decaying H-upper to the right of the critical strip: `2 ≤ Re z ≤ σ₁`, `|Im z| ≥ 2`. -/
theorem exists_H_upper_right (σ₁ : ℝ) (hσ₁ : 2 ≤ σ₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ, ∀ z : ℂ, 2 ≤ z.re → z.re ≤ σ₁ → 2 ≤ |z.im| →
      ‖completedDedekindZetaEntire K z‖
        ≤ C * (1 + |z.im|)^P
          * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |z.im|)) / 4) := by
  obtain ⟨Cγ, hCγ, Pγ, hγ⟩ := exists_norm_gammaFactor_le_range K σ₁
  set T₂ : ℝ := ∑' n : ℕ, ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖ with hT₂
  have hT₂0 : 0 ≤ T₂ := tsum_nonneg (fun n => norm_nonneg _)
  have hdne : ((discr K : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.discr_ne_zero K
  have hd1 : (1:ℝ) ≤ |((discr K : ℤ) : ℝ)| := by
    have := Int.one_le_abs (NumberField.discr_ne_zero K)
    calc (1:ℝ) = ((1:ℤ) : ℝ) := by norm_num
      _ ≤ ((|discr K| : ℤ) : ℝ) := by exact_mod_cast this
      _ = |((discr K : ℤ) : ℝ)| := by push_cast; rfl
  refine ⟨(σ₁ + 2)^2 * |((discr K : ℤ) : ℝ)| ^ (σ₁/2) * Cγ * (T₂ + 1),
    by positivity, Pγ + 2, fun z h2 hσr ht => ?_⟩
  set σ : ℝ := z.re with hσ
  set t : ℝ := z.im with htdef
  have hzeq : z = (σ : ℂ) + (t : ℂ) * Complex.I := by
    rw [hσ, htdef, Complex.re_add_im]
  have hs0 : z ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [← hσ] at this
    simp at this
    rw [this] at h2
    norm_num at h2
  have hs1 : z ≠ 1 := by
    intro h0
    have := congrArg Complex.re h0
    rw [← hσ] at this
    simp at this
    rw [this] at h2
    norm_num at h2
  have hsre1 : (1:ℝ) < z.re := by rw [← hσ]; linarith
  rw [completedDedekindZetaEntire_eq K hs0 hs1,
    completedDedekindZeta_eq_of_one_lt_re K hsre1, completedZetaPrefactor]
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have h1t : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hzn : ‖z‖ ≤ (σ₁ + 2) * (1 + |t|) := by
    rw [hzeq]
    exact (norm_ofReal_add_mul_I_le σ t (by linarith)).trans (by nlinarith [abs_nonneg t])
  have hzn1 : ‖z - 1‖ ≤ (σ₁ + 2) * (1 + |t|) := by
    have hz1eq : z - 1 = ((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
      rw [hzeq]
      push_cast
      ring
    rw [hz1eq]
    exact (norm_ofReal_add_mul_I_le (σ - 1) t (by linarith)).trans (by nlinarith [abs_nonneg t])
  have hΔ : ‖((|discr K| : ℝ) : ℂ) ^ (z / 2)‖ ≤ |((discr K : ℤ) : ℝ)| ^ (σ₁/2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [abs_pos.mpr hdne])]
    have hre2 : (z / 2).re = σ/2 := by
      rw [show z / 2 = ((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I by
        rw [hzeq]; push_cast; ring]
      simp
    rw [hre2]
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  have hγb : ‖gammaFactor K z‖ ≤ Cγ * (1 + |t|)^Pγ
      * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |t|)) / 4) := by
    rw [hzeq]
    exact hγ σ t (by linarith) hσr ht
  have hζb : ‖dedekindZeta K z‖ ≤ T₂ + 1 := by
    refine le_trans (norm_dedekindZeta_le_of_two_le_re K (s := z) (by rw [← hσ]; linarith)) ?_
    rw [← hT₂]
    linarith
  calc ‖z‖ * ‖z - 1‖ * (‖((|discr K| : ℝ) : ℂ) ^ (z / 2)‖ * ‖gammaFactor K z‖
        * ‖dedekindZeta K z‖)
      ≤ ((σ₁ + 2) * (1 + |t|)) * ((σ₁ + 2) * (1 + |t|))
        * ((|((discr K : ℤ) : ℝ)| ^ (σ₁/2))
          * (Cγ * (1 + |t|)^Pγ
            * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |t|)) / 4))
          * (T₂ + 1)) := by
        gcongr
    _ = (σ₁ + 2)^2 * |((discr K : ℤ) : ℝ)| ^ (σ₁/2) * Cγ * (T₂ + 1)
        * (1 + |t|)^(Pγ + 2)
        * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |t|)) / 4) := by
        rw [pow_add]
        ring

/-- Sphere-sup bound for the Jensen ball: at center `A+iT` with radius `A+1`, every
point of the closed ball satisfies the decaying envelope bound (in terms of `|T|`). -/
theorem exists_H_ball_sup (A : ℝ) (hA : 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ, ∀ T : ℝ, A + 5 ≤ |T| →
      ∀ z ∈ Metric.closedBall ((A : ℂ) + (T : ℂ) * Complex.I) (A + 1),
        ‖completedDedekindZetaEntire K z‖
          ≤ C * (1 + |T|)^P
            * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |T|)) / 4) := by
  obtain ⟨C₁, hC₁, hstrip⟩ := exists_H_strip_decay K
  obtain ⟨C₂, hC₂, P₂, hright⟩ := exists_H_upper_right K (2*A + 2) (by linarith)
  set n : ℕ := gammaExponent K with hn
  refine ⟨(C₁ + C₂) * (2 + A)^(n + 2 + P₂)
    * Real.exp (((n:ℕ) : ℝ) * (π * (A + 1)) / 4), by positivity,
    n + 2 + P₂, fun T hT z hz => ?_⟩
  rw [Metric.mem_closedBall] at hz
  -- coordinates of z
  have hre : |z.re - A| ≤ A + 1 := by
    have h1 : |(z - ((A : ℂ) + (T : ℂ) * Complex.I)).re| ≤ A + 1 := by
      refine le_trans (Complex.abs_re_le_norm _) ?_
      rw [Complex.dist_eq] at hz
      exact hz
    have h2 : (z - ((A : ℂ) + (T : ℂ) * Complex.I)).re = z.re - A := by simp
    rwa [h2] at h1
  have him : |z.im - T| ≤ A + 1 := by
    have h1 : |(z - ((A : ℂ) + (T : ℂ) * Complex.I)).im| ≤ A + 1 := by
      refine le_trans (Complex.abs_im_le_norm _) ?_
      rw [Complex.dist_eq] at hz
      exact hz
    have h2 : (z - ((A : ℂ) + (T : ℂ) * Complex.I)).im = z.im - T := by simp
    rwa [h2] at h1
  have hzre1 : -1 ≤ z.re := by
    have := abs_le.mp hre
    linarith [this.1]
  have hzre2 : z.re ≤ 2*A + 1 := by
    have := abs_le.mp hre
    linarith [this.2]
  -- |z.im| is comparable to |T|
  have himlow : |T| - (A + 1) ≤ |z.im| := by
    have h1 : |T| - |z.im| ≤ |z.im - T| := by
      calc |T| - |z.im| ≤ |T - z.im| := abs_sub_abs_le_abs_sub T z.im
        _ = |z.im - T| := abs_sub_comm T z.im
    linarith
  have himup : |z.im| ≤ |T| + (A + 1) := by
    have h1 : |z.im| - |T| ≤ |z.im - T| := abs_sub_abs_le_abs_sub z.im T
    linarith
  have him2 : 2 ≤ |z.im| := by linarith
  have him1t : 1 + |z.im| ≤ (2 + A) * (1 + |T|) := by
    have h1T : (1:ℝ) ≤ |T| := by linarith
    nlinarith
  -- envelope transfer from |z.im| to |T|
  have henv : Real.exp (-(((n:ℕ) : ℝ) * (π * |z.im|)) / 4)
      ≤ Real.exp (((n:ℕ) : ℝ) * (π * (A + 1)) / 4)
        * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have hπ0 : (0:ℝ) ≤ π := Real.pi_pos.le
    have hn0 : (0:ℝ) ≤ (n:ℕ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg hn0 hπ0]
  -- the two regimes
  have hcase : ‖completedDedekindZetaEntire K z‖
      ≤ (C₁ + C₂) * (1 + |z.im|)^(n + 2 + P₂)
        * Real.exp (-(((n:ℕ) : ℝ) * (π * |z.im|)) / 4) := by
    have h1z : (1:ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
    rcases le_or_gt z.re 2 with hzcase | hzcase
    · have hb := hstrip z hzre1 hzcase (by linarith [him2])
      refine le_trans hb ?_
      refine mul_le_mul (mul_le_mul (by linarith) (pow_le_pow_right₀ h1z (by omega))
        (by positivity) (by linarith)) le_rfl (by positivity) (by positivity)
    · have hb := hright z (le_of_lt hzcase) (by linarith [hzre2]) him2
      refine le_trans hb ?_
      refine mul_le_mul (mul_le_mul (by linarith) (pow_le_pow_right₀ h1z (by omega))
        (by positivity) (by linarith)) le_rfl (by positivity) (by positivity)
  refine le_trans hcase ?_
  calc (C₁ + C₂) * (1 + |z.im|)^(n + 2 + P₂)
      * Real.exp (-(((n:ℕ) : ℝ) * (π * |z.im|)) / 4)
      ≤ (C₁ + C₂) * ((2 + A) * (1 + |T|))^(n + 2 + P₂)
        * (Real.exp (((n:ℕ) : ℝ) * (π * (A + 1)) / 4)
          * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) him1t _) (by positivity))
          henv (by positivity) (by positivity)
    _ = (C₁ + C₂) * (2 + A)^(n + 2 + P₂)
        * Real.exp (((n:ℕ) : ℝ) * (π * (A + 1)) / 4)
        * (1 + |T|)^(n + 2 + P₂)
        * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) := by
        rw [mul_pow]
        ring

/-- **AC-A4: per-height zero counting.** There are an abscissa `A` and a constant `C`
such that for all heights `|T| ≥ A+5`, the number of zeros of `H` (with multiplicity)
in the closed ball of radius `√(A²+1)` around `A+iT` — a ball containing the critical
slab `0 ≤ Re ≤ 1`, `|Im - T| ≤ 1` — is at most `C·log(2+|T|)`. -/
theorem exists_ball_zero_count :
    ∃ A : ℝ, 2 ≤ A ∧ ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, A + 5 ≤ |T| →
      ((∑ᶠ u, (MeromorphicOn.divisor (completedDedekindZetaEntire K)
          (Metric.closedBall ((A : ℂ) + (T : ℂ) * Complex.I) (Real.sqrt (A^2+1)))) u : ℤ)
        : ℝ) ≤ C * Real.log (2 + |T|) := by
  obtain ⟨A, hA2, cL, hcL, hlow⟩ := exists_H_center_lower K
  obtain ⟨cB, hcB, P, hball⟩ := exists_H_ball_sup K A hA2
  set n : ℕ := gammaExponent K with hn
  set Pn : ℕ := nrRealPlaces K + nrComplexPlaces K with hPn
  -- the ratio constant
  set Cr : ℝ := cB / cL + 1 with hCr
  have hCr1 : 1 ≤ Cr := by
    rw [hCr]
    have : 0 ≤ cB / cL := by positivity
    linarith
  -- geometry
  have hApos : (0:ℝ) < A := by linarith
  have hrpos : (0:ℝ) < Real.sqrt (A^2+1) := by positivity
  have hrR : Real.sqrt (A^2+1) < A + 1 := by
    rw [show A + 1 = Real.sqrt ((A+1)^2) by
      rw [Real.sqrt_sq (by linarith)]]
    refine Real.sqrt_lt_sqrt (by positivity) ?_
    nlinarith
  have hlogRr : 0 < Real.log ((A+1) / Real.sqrt (A^2+1)) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hrpos]
    linarith [hrR]
  refine ⟨A, hA2, (Real.log Cr + (P + Pn + 1))
    / Real.log ((A+1) / Real.sqrt (A^2+1)),
    div_pos (by nlinarith [Real.log_nonneg hCr1, Nat.cast_nonneg (α := ℝ) P,
      Nat.cast_nonneg (α := ℝ) Pn]) hlogRr, fun T hT => ?_⟩
  set c : ℂ := (A : ℂ) + (T : ℂ) * Complex.I with hc
  have hT2 : 2 ≤ |T| := by linarith
  -- center value and its lower bound
  have hHc := hlow T hT2
  have hHcpos : 0 < ‖completedDedekindZetaEntire K c‖ := by
    refine lt_of_lt_of_le ?_ hHc
    positivity
  have hHcne : completedDedekindZetaEntire K c ≠ 0 := by
    intro h0
    rw [h0] at hHcpos
    simp at hHcpos
  -- the normalized function
  set g : ℂ → ℂ := fun z =>
    (completedDedekindZetaEntire K c)⁻¹ * completedDedekindZetaEntire K z with hg
  have hganal : AnalyticOnNhd ℂ g (Metric.closedBall c |A+1|) := by
    intro z _
    exact analyticAt_const.mul ((differentiable_completedDedekindZetaEntire K).analyticAt z)
  have hgc : g c = 1 := by
    rw [hg]
    field_simp
  -- sphere bound for g
  have hM1 : (1:ℝ) ≤ Cr * (1 + |T|)^(P + Pn) := by
    have h1T : (1:ℝ) ≤ 1 + |T| := by linarith [abs_nonneg T]
    calc (1:ℝ) = 1 * 1 := by norm_num
      _ ≤ Cr * (1 + |T|)^(P + Pn) :=
          mul_le_mul hCr1 (one_le_pow₀ h1T) (by norm_num) (by linarith)
  have hgbound : ∀ z ∈ Metric.sphere c |A+1|, ‖g z‖ ≤ Cr * (1 + |T|)^(P + Pn) := by
    intro z hz
    have hzball : z ∈ Metric.closedBall c (A+1) := by
      rw [Metric.mem_closedBall]
      rw [Metric.mem_sphere] at hz
      rw [hz, abs_of_pos (by linarith : (0:ℝ) < A + 1)]
    have hup := hball T hT z hzball
    rw [hg]
    rw [norm_mul, norm_inv]
    -- ‖H c‖⁻¹·‖H z‖ ≤ [cB(1+T)^P E]/[cL·E/(1+T)^{Pn}] = (cB/cL)(1+T)^{P+Pn}
    have hE : (0:ℝ) < Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) := Real.exp_pos _
    have hinv : ‖completedDedekindZetaEntire K c‖⁻¹
        ≤ ((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) := by
      rw [inv_le_iff_one_le_mul₀ hHcpos]
      have hstep : cL * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) / (1 + |T|)^Pn
          * (((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4)) = 1 := by
        field_simp
      calc (1:ℝ) = cL * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) / (1 + |T|)^Pn
          * (((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4)) :=
            hstep.symm
        _ ≤ ‖completedDedekindZetaEntire K c‖
            * (((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4)) := by
            refine mul_le_mul_of_nonneg_right hHc (by positivity)
        _ = (((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4))
            * ‖completedDedekindZetaEntire K c‖ := by ring
    calc ‖completedDedekindZetaEntire K c‖⁻¹ * ‖completedDedekindZetaEntire K z‖
        ≤ (((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4))
          * (cB * (1 + |T|)^P * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4)) :=
          mul_le_mul hinv hup (norm_nonneg _) (by positivity)
      _ = cB / cL * (1 + |T|)^(P + Pn) := by
          rw [show P + Pn = Pn + P by ring, pow_add]
          field_simp
          ring
      _ ≤ Cr * (1 + |T|)^(P + Pn) :=
          mul_le_mul_of_nonneg_right (by rw [hCr]; linarith) (by positivity)
  -- Jensen counting for g
  have habs_r : |Real.sqrt (A^2+1)| = Real.sqrt (A^2+1) := abs_of_pos hrpos
  have habs_R : |A+1| = A+1 := abs_of_pos (by linarith : (0:ℝ) < A + 1)
  have hcount := AnalyticOnNhd.sum_divisor_le
    (c := c) (r := Real.sqrt (A^2+1)) (R := A+1) (M := Cr * (1 + |T|)^(P + Pn)) (f := g)
    (by rw [habs_r]; exact hrpos)
    (by rw [habs_r, habs_R]; exact hrR)
    hM1 hganal (by rw [hgc]; norm_num) hgbound
  -- divisor transfer to H
  have hHmero : MeromorphicOn (completedDedekindZetaEntire K)
      (Metric.closedBall c |Real.sqrt (A^2+1)|) := fun z _ =>
    ((differentiable_completedDedekindZetaEntire K).analyticAt z).meromorphicAt
  have hconstmero : MeromorphicOn (fun _ : ℂ => (completedDedekindZetaEntire K c)⁻¹)
      (Metric.closedBall c |Real.sqrt (A^2+1)|) := fun z _ =>
    analyticAt_const.meromorphicAt
  have hordc : ∀ z ∈ Metric.closedBall c |Real.sqrt (A^2+1)|,
      meromorphicOrderAt (fun _ : ℂ => (completedDedekindZetaEntire K c)⁻¹) z ≠ ⊤ := by
    intro z _
    classical
    rw [meromorphicOrderAt_const, if_neg (inv_ne_zero hHcne)]
    exact WithTop.zero_ne_top
  have hcmem : c ∈ Metric.closedBall c |Real.sqrt (A^2+1)| := by
    rw [habs_r]
    exact Metric.mem_closedBall_self hrpos.le
  have hordHc : meromorphicOrderAt (completedDedekindZetaEntire K) c ≠ ⊤ := by
    rw [((differentiable_completedDedekindZetaEntire K).analyticAt c).meromorphicOrderAt_eq]
    have h0 : analyticOrderAt (completedDedekindZetaEntire K) c = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hHcne)
    rw [h0]
    simp
  have hordH : ∀ z ∈ Metric.closedBall c |Real.sqrt (A^2+1)|,
      meromorphicOrderAt (completedDedekindZetaEntire K) z ≠ ⊤ := by
    intro z hz
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hHmero
      ((convex_closedBall _ _).isPreconnected) hcmem hz hordHc
  have hdiv : MeromorphicOn.divisor g (Metric.closedBall c |Real.sqrt (A^2+1)|)
      = MeromorphicOn.divisor (completedDedekindZetaEntire K)
        (Metric.closedBall c |Real.sqrt (A^2+1)|) := by
    have hgdef : g = fun z => (fun _ : ℂ => (completedDedekindZetaEntire K c)⁻¹) z
        * completedDedekindZetaEntire K z := rfl
    rw [hgdef, MeromorphicOn.divisor_fun_mul hconstmero hHmero hordc hordH,
      MeromorphicOn.divisor_const]
    simp
  rw [hdiv] at hcount
  rw [habs_r] at hcount
  refine le_trans hcount ?_
  -- the log-quotient bound
  rw [hgc, norm_one, div_one]
  have h1T : (1:ℝ) ≤ 1 + |T| := by linarith [abs_nonneg T]
  have hL1 : (1:ℝ) ≤ Real.log (2 + |T|) := by
    have he9 : Real.exp 1 ≤ 2 + |T| := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 + |T|) := Real.log_le_log (Real.exp_pos 1) he9
  have hlogM : Real.log (Cr * (1 + |T|)^(P + Pn))
      ≤ (Real.log Cr + (P + Pn + 1)) * Real.log (2 + |T|) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hlog1 : Real.log (1 + |T|) ≤ Real.log (2 + |T|) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlogCr : (0:ℝ) ≤ Real.log Cr := Real.log_nonneg hCr1
    have hPP : (0:ℝ) ≤ ((P + Pn : ℕ) : ℝ) := Nat.cast_nonneg _
    calc Real.log Cr + ((P + Pn : ℕ) : ℝ) * Real.log (1 + |T|)
        ≤ Real.log Cr * Real.log (2 + |T|)
          + ((P + Pn : ℕ) : ℝ) * Real.log (2 + |T|) := by
          have h1 : Real.log Cr ≤ Real.log Cr * Real.log (2 + |T|) := by
            nlinarith
          have h2 : ((P + Pn : ℕ) : ℝ) * Real.log (1 + |T|)
              ≤ ((P + Pn : ℕ) : ℝ) * Real.log (2 + |T|) :=
            mul_le_mul_of_nonneg_left hlog1 hPP
          linarith
      _ ≤ (Real.log Cr + (P + Pn + 1)) * Real.log (2 + |T|) := by
          push_cast
          nlinarith
  calc Real.log (Cr * (1 + |T|)^(P + Pn)) / Real.log ((A+1) / Real.sqrt (A^2+1))
      ≤ ((Real.log Cr + (P + Pn + 1)) * Real.log (2 + |T|))
        / Real.log ((A+1) / Real.sqrt (A^2+1)) := by
        gcongr
    _ = (Real.log Cr + (P + Pn + 1)) / Real.log ((A+1) / Real.sqrt (A^2+1))
        * Real.log (2 + |T|) := by ring

/-- **Holomorphic logarithm on a convex open set** (A5-i): a zero-free holomorphic
function on a nonempty convex open set has a holomorphic logarithm. The continuous
branch comes from mathlib's simply-connected lifting; differentiability is local, via
the principal branch of the quotient. -/
theorem exists_differentiableOn_log {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hne : U.Nonempty) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (h0 : ∀ z ∈ U, f z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ Set.EqOn (Complex.exp ∘ L) f U := by
  have hcontr : ContractibleSpace U := hUc.contractibleSpace hne
  have hSC : IsSimplyConnected U := (inferInstance : SimplyConnectedSpace U)
  obtain ⟨L, hLc, hLeq⟩ := Complex.exists_continuousOn_eqOn_exp_comp hSC hUo
    hf.continuousOn (by
      rintro ⟨z, hz, hz0⟩
      exact h0 z hz hz0)
  refine ⟨L, fun z₀ hz₀ => ?_, hLeq⟩
  have hUmem : U ∈ nhds z₀ := hUo.mem_nhds hz₀
  suffices h : DifferentiableAt ℂ L z₀ from h.differentiableWithinAt
  have hf0 : f z₀ ≠ 0 := h0 z₀ hz₀
  have hfat : DifferentiableAt ℂ f z₀ := hf.differentiableAt hUmem
  have hquot : ContinuousAt (fun z => f z / f z₀) z₀ :=
    (hf.continuousOn.continuousAt hUmem).div_const _
  have hone : f z₀ / f z₀ = 1 := by field_simp
  have hslit : f z₀ / f z₀ ∈ Complex.slitPlane := by
    rw [hone]
    simp [Complex.slitPlane]
  have hDcont : ContinuousAt
      (fun z => L z - (L z₀ + Complex.log (f z / f z₀))) z₀ :=
    (hLc.continuousAt hUmem).sub (continuousAt_const.add (hquot.clog hslit))
  have hD0 : L z₀ - (L z₀ + Complex.log (f z₀ / f z₀)) = 0 := by
    rw [hone, Complex.log_one]
    ring
  -- values of D lie in 2πiℤ
  have hDint : ∀ z ∈ U, ∃ n : ℤ,
      L z - (L z₀ + Complex.log (f z / f z₀)) = n * (2 * π * Complex.I) := by
    intro z hz
    have hexpD : Complex.exp (L z - (L z₀ + Complex.log (f z / f z₀))) = 1 := by
      rw [Complex.exp_sub, Complex.exp_add,
        Complex.exp_log (div_ne_zero (h0 z hz) hf0)]
      have h1 : Complex.exp (L z) = f z := hLeq hz
      have h2 : Complex.exp (L z₀) = f z₀ := hLeq hz₀
      rw [h1, h2]
      field_simp [h0 z hz, hf0]
    rwa [Complex.exp_eq_one_iff] at hexpD
  -- D is eventually small, hence eventually zero
  have hDsmall : ∀ᶠ z in nhds z₀,
      ‖L z - (L z₀ + Complex.log (f z / f z₀))‖ < 2*π := by
    have htend := hDcont.tendsto
    rw [hD0] at htend
    have := Metric.tendsto_nhds.mp htend (2*π) (by positivity)
    filter_upwards [this] with z hz
    rwa [dist_zero_right] at hz
  have hDzero : (fun z => L z₀ + Complex.log (f z / f z₀)) =ᶠ[nhds z₀] L := by
    filter_upwards [hDsmall, hUmem] with z hznorm hzU
    obtain ⟨n, hn⟩ := hDint z hzU
    have hnz : (n : ℂ) = 0 := by
      by_contra hne'
      have hn1 : (1:ℝ) ≤ |(n:ℝ)| := by
        have : n ≠ 0 := by exact_mod_cast hne'
        exact_mod_cast Int.one_le_abs this
      rw [hn] at hznorm
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_intCast, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hznorm
      nlinarith [Real.pi_pos]
    rw [hnz, zero_mul] at hn
    linear_combination -hn
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hDzero.symm
  exact (differentiableAt_const _).add ((hfat.div_const _).clog hslit)

/-- Codiscrete-within agreement of continuous functions on an open set upgrades to
genuine agreement (ℂ has no isolated points). -/
theorem eqOn_of_eventuallyEq_codiscreteWithin {f₁ f₂ : ℂ → ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (h : f₁ =ᶠ[Filter.codiscreteWithin U] f₂)
    (h₁ : ContinuousOn f₁ U) (h₂ : ContinuousOn f₂ U) : Set.EqOn f₁ f₂ U := by
  intro z hz
  by_contra hne
  -- on a neighborhood of z inside U, the two functions differ
  have hcont : ContinuousAt (fun w => f₁ w - f₂ w) z :=
    ((h₁.continuousAt (hUo.mem_nhds hz)).sub (h₂.continuousAt (hUo.mem_nhds hz)))
  have hne' : f₁ z - f₂ z ≠ 0 := sub_ne_zero_of_ne hne
  have hV : ∀ᶠ w in nhds z, f₁ w - f₂ w ≠ 0 :=
    hcont.eventually_ne hne'
  have hVU : ∀ᶠ w in nhds z, w ∈ U ∧ f₁ w ≠ f₂ w := by
    filter_upwards [hUo.mem_nhds hz, hV] with w hw hw'
    exact ⟨hw, sub_ne_zero.mp hw'⟩
  -- hence U \ {agreement set} accumulates at z
  have hacc : AccPt z (Filter.principal (U \ {x | f₁ x = f₂ x})) := by
    rw [AccPt]
    have hmem : U \ {x | f₁ x = f₂ x} ∈ nhdsWithin z {z}ᶜ := by
      rw [nhdsWithin]
      refine Filter.mem_inf_of_left ?_
      filter_upwards [hVU] with w hw
      exact ⟨hw.1, hw.2⟩
    have heq : (nhdsWithin z {z}ᶜ ⊓ Filter.principal (U \ {x | f₁ x = f₂ x}))
        = nhdsWithin z {z}ᶜ := by
      rw [inf_eq_left]
      exact Filter.le_principal_iff.mpr hmem
    rw [heq]
    infer_instance
  have hcod := mem_codiscreteWithin_accPt.mp h
  exact hcod z hz hacc

/-- **Zero-peeling on a ball** (A5-ii-b): on an open ball where `H` is not identically
zero, `H` factors as the divisor product times a zero-free analytic function. -/
theorem exists_H_ball_factorization (c : ℂ) {R : ℝ}
    {w : ℂ} (hw : w ∈ Metric.ball c R)
    (hHw : completedDedekindZetaEntire K w ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball c R)
      ∧ (∀ z ∈ Metric.ball c R, g z ≠ 0)
      ∧ ∀ z ∈ Metric.ball c R,
          completedDedekindZetaEntire K z
            = (∏ᶠ u, (z - u) ^ ((MeromorphicOn.divisor (completedDedekindZetaEntire K)
                (Metric.ball c R)) u)) * g z := by
  set U : Set ℂ := Metric.ball c R with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have hHmero : MeromorphicOn (completedDedekindZetaEntire K) U := fun z _ =>
    ((differentiable_completedDedekindZetaEntire K).analyticAt z).meromorphicAt
  have hordw : meromorphicOrderAt (completedDedekindZetaEntire K) w ≠ ⊤ := by
    rw [((differentiable_completedDedekindZetaEntire K).analyticAt w).meromorphicOrderAt_eq]
    have h0 : analyticOrderAt (completedDedekindZetaEntire K) w = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hHw)
    rw [h0]
    simp
  have hord : ∀ u : U, meromorphicOrderAt (completedDedekindZetaEntire K) u ≠ ⊤ := by
    intro u
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hHmero
      ((convex_ball _ _).isPreconnected) hw u.2 hordw
  have hfin : ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U)).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset
      (fun z _ => ((differentiable_completedDedekindZetaEntire K).analyticAt z).meromorphicAt)
      (isCompact_closedBall c R) Metric.ball_subset_closedBall
  obtain ⟨g, hganal, hgne, heq⟩ :=
    MeromorphicOn.extract_zeros_poles hHmero hord hfin
  have hfinsupp : Function.HasFiniteSupport
      ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U) : ℂ → ℤ) := hfin
  -- nonnegativity of the divisor (H analytic)
  have hdivpos : ∀ u : ℂ,
      0 ≤ (MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u := by
    intro u
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ =>
      (differentiable_completedDedekindZetaEntire K).analyticAt z)) u
  -- continuity of the divisor product
  have hprodanal : ∀ z : ℂ, AnalyticAt ℂ
      (∏ᶠ u, (· - u) ^ ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u)) z :=
    fun z => Function.FactorizedRational.analyticAt (hdivpos z)
  -- upgrade the codiscrete agreement to genuine agreement
  have heqOn : Set.EqOn (completedDedekindZetaEntire K)
      ((∏ᶠ u, (· - u) ^ ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u))
        • g) U := by
    refine eqOn_of_eventuallyEq_codiscreteWithin hUo heq
      (differentiable_completedDedekindZetaEntire K).continuous.continuousOn ?_
    simpa only [smul_eq_mul] using ContinuousOn.mul
      (fun z _ => (hprodanal z).continuousAt.continuousWithinAt) hganal.continuousOn
  refine ⟨g, hganal, fun z hz => hgne ⟨z, hz⟩, fun z hz => ?_⟩
  have := heqOn hz
  rw [this, Pi.smul_apply', smul_eq_mul]
  congr 1
  rw [Function.FactorizedRational.finprod_eq_fun hfinsupp]

/-- Sphere-sup bound for the Landau ball: at center `A+iT` with the larger radius
`A+3`, every point of the closed ball satisfies the decaying envelope bound (in
terms of `|T|`). Left of the critical strip the functional equation reflects the
bound from the right half-plane. -/
theorem exists_H_ball_sup_big (A : ℝ) (hA : 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ, ∀ T : ℝ, A + 5 ≤ |T| →
      ∀ z ∈ Metric.closedBall ((A : ℂ) + (T : ℂ) * Complex.I) (A + 3),
        ‖completedDedekindZetaEntire K z‖
          ≤ C * (1 + |T|)^P
            * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |T|)) / 4) := by
  obtain ⟨C₁, hC₁, hstrip⟩ := exists_H_strip_decay K
  obtain ⟨C₂, hC₂, P₂, hright⟩ := exists_H_upper_right K (2*A + 3) (by linarith)
  set n : ℕ := gammaExponent K with hn
  refine ⟨(C₁ + C₂) * (4 + A)^(n + 2 + P₂)
    * Real.exp (((n:ℕ) : ℝ) * (π * (A + 3)) / 4), by positivity,
    n + 2 + P₂, fun T hT z hz => ?_⟩
  rw [Metric.mem_closedBall] at hz
  -- coordinates of z
  have hre : |z.re - A| ≤ A + 3 := by
    have h1 : |(z - ((A : ℂ) + (T : ℂ) * Complex.I)).re| ≤ A + 3 := by
      refine le_trans (Complex.abs_re_le_norm _) ?_
      rw [Complex.dist_eq] at hz
      exact hz
    have h2 : (z - ((A : ℂ) + (T : ℂ) * Complex.I)).re = z.re - A := by simp
    rwa [h2] at h1
  have him : |z.im - T| ≤ A + 3 := by
    have h1 : |(z - ((A : ℂ) + (T : ℂ) * Complex.I)).im| ≤ A + 3 := by
      refine le_trans (Complex.abs_im_le_norm _) ?_
      rw [Complex.dist_eq] at hz
      exact hz
    have h2 : (z - ((A : ℂ) + (T : ℂ) * Complex.I)).im = z.im - T := by simp
    rwa [h2] at h1
  have hzre1 : -3 ≤ z.re := by
    have := abs_le.mp hre
    linarith [this.1]
  have hzre2 : z.re ≤ 2*A + 3 := by
    have := abs_le.mp hre
    linarith [this.2]
  -- |z.im| is comparable to |T|
  have himlow : |T| - (A + 3) ≤ |z.im| := by
    have h1 : |T| - |z.im| ≤ |z.im - T| := by
      calc |T| - |z.im| ≤ |T - z.im| := abs_sub_abs_le_abs_sub T z.im
        _ = |z.im - T| := abs_sub_comm T z.im
    linarith
  have himup : |z.im| ≤ |T| + (A + 3) := by
    have h1 : |z.im| - |T| ≤ |z.im - T| := abs_sub_abs_le_abs_sub z.im T
    linarith
  have him2 : 2 ≤ |z.im| := by linarith
  have him1t : 1 + |z.im| ≤ (4 + A) * (1 + |T|) := by
    have h1T : (1:ℝ) ≤ |T| := by linarith
    nlinarith
  -- envelope transfer from |z.im| to |T|
  have henv : Real.exp (-(((n:ℕ) : ℝ) * (π * |z.im|)) / 4)
      ≤ Real.exp (((n:ℕ) : ℝ) * (π * (A + 3)) / 4)
        * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have hπ0 : (0:ℝ) ≤ π := Real.pi_pos.le
    have hn0 : (0:ℝ) ≤ (n:ℕ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg hn0 hπ0]
  -- the three regimes
  have hcase : ‖completedDedekindZetaEntire K z‖
      ≤ (C₁ + C₂) * (1 + |z.im|)^(n + 2 + P₂)
        * Real.exp (-(((n:ℕ) : ℝ) * (π * |z.im|)) / 4) := by
    have h1z : (1:ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
    rcases le_or_gt z.re 2 with hzcase | hzcase
    · rcases le_or_gt (-1) z.re with hzleft | hzleft
      · -- critical strip: direct decay bound
        have hb := hstrip z hzleft hzcase (by linarith [him2])
        refine le_trans hb ?_
        refine mul_le_mul (mul_le_mul (by linarith) (pow_le_pow_right₀ h1z (by omega))
          (by positivity) (by linarith)) le_rfl (by positivity) (by positivity)
      · -- left of the strip: reflect via the functional equation
        have hfe : completedDedekindZetaEntire K z
            = completedDedekindZetaEntire K (1 - z) :=
          (completedDedekindZetaEntire_one_sub K z).symm
        have hre1z : (1 - z).re = 1 - z.re := by simp
        have him1z : |(1 - z).im| = |z.im| := by
          have : (1 - z).im = -z.im := by simp
          rw [this, abs_neg]
        have hb := hright (1 - z) (by rw [hre1z]; linarith)
          (by rw [hre1z]; linarith) (by rw [him1z]; exact him2)
        rw [hfe]
        rw [him1z] at hb
        refine le_trans hb ?_
        refine mul_le_mul (mul_le_mul (by linarith) (pow_le_pow_right₀ h1z (by omega))
          (by positivity) (by linarith)) le_rfl (by positivity) (by positivity)
    · -- right of the strip
      have hb := hright z (le_of_lt hzcase) (by linarith [hzre2]) him2
      refine le_trans hb ?_
      refine mul_le_mul (mul_le_mul (by linarith) (pow_le_pow_right₀ h1z (by omega))
        (by positivity) (by linarith)) le_rfl (by positivity) (by positivity)
  refine le_trans hcase ?_
  calc (C₁ + C₂) * (1 + |z.im|)^(n + 2 + P₂)
      * Real.exp (-(((n:ℕ) : ℝ) * (π * |z.im|)) / 4)
      ≤ (C₁ + C₂) * ((4 + A) * (1 + |T|))^(n + 2 + P₂)
        * (Real.exp (((n:ℕ) : ℝ) * (π * (A + 3)) / 4)
          * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) him1t _) (by positivity))
          henv (by positivity) (by positivity)
    _ = (C₁ + C₂) * (4 + A)^(n + 2 + P₂)
        * Real.exp (((n:ℕ) : ℝ) * (π * (A + 3)) / 4)
        * (1 + |T|)^(n + 2 + P₂)
        * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) := by
        rw [mul_pow]
        ring

/-- **Per-height zero counting at the Landau radius.** Given the abscissa `A` with the
envelope-matched center lower bound, the number of zeros of `H` (with multiplicity) in
the closed ball of radius `A+2` around `A+iT` is at most `C·log(2+|T|)`. Parametric in
`A` and the center bound so that downstream users can share one `A`. -/
theorem exists_ball_zero_count_big (A : ℝ) (hA2 : 2 ≤ A) (cL : ℝ) (hcL : 0 < cL)
    (hlow : ∀ t : ℝ, 2 ≤ |t| →
      cL * Real.exp (-(((gammaExponent K : ℕ) : ℝ) * (π * |t|)) / 4)
        / (1 + |t|)^(nrRealPlaces K + nrComplexPlaces K)
        ≤ ‖completedDedekindZetaEntire K ((A : ℂ) + (t : ℂ) * Complex.I)‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, A + 5 ≤ |T| →
      ((∑ᶠ u, (MeromorphicOn.divisor (completedDedekindZetaEntire K)
          (Metric.closedBall ((A : ℂ) + (T : ℂ) * Complex.I) (A + 2))) u : ℤ)
        : ℝ) ≤ C * Real.log (2 + |T|) := by
  obtain ⟨cB, hcB, P, hball⟩ := exists_H_ball_sup_big K A hA2
  set n : ℕ := gammaExponent K with hn
  set Pn : ℕ := nrRealPlaces K + nrComplexPlaces K with hPn
  -- the ratio constant
  set Cr : ℝ := cB / cL + 1 with hCr
  have hCr1 : 1 ≤ Cr := by
    rw [hCr]
    have : 0 ≤ cB / cL := by positivity
    linarith
  -- geometry
  have hApos : (0:ℝ) < A := by linarith
  have hrpos : (0:ℝ) < A + 2 := by linarith
  have hrR : A + 2 < A + 3 := by linarith
  have hlogRr : 0 < Real.log ((A+3) / (A+2)) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hrpos]
    linarith
  refine ⟨(Real.log Cr + (P + Pn + 1)) / Real.log ((A+3) / (A+2)),
    div_pos (by nlinarith [Real.log_nonneg hCr1, Nat.cast_nonneg (α := ℝ) P,
      Nat.cast_nonneg (α := ℝ) Pn]) hlogRr, fun T hT => ?_⟩
  set c : ℂ := (A : ℂ) + (T : ℂ) * Complex.I with hc
  have hT2 : 2 ≤ |T| := by linarith
  -- center value and its lower bound
  have hHc := hlow T hT2
  have hHcpos : 0 < ‖completedDedekindZetaEntire K c‖ := by
    refine lt_of_lt_of_le ?_ hHc
    positivity
  have hHcne : completedDedekindZetaEntire K c ≠ 0 := by
    intro h0
    rw [h0] at hHcpos
    simp at hHcpos
  -- the normalized function
  set g : ℂ → ℂ := fun z =>
    (completedDedekindZetaEntire K c)⁻¹ * completedDedekindZetaEntire K z with hg
  have hganal : AnalyticOnNhd ℂ g (Metric.closedBall c |A+3|) := by
    intro z _
    exact analyticAt_const.mul ((differentiable_completedDedekindZetaEntire K).analyticAt z)
  have hgc : g c = 1 := by
    rw [hg]
    field_simp
  -- sphere bound for g
  have hM1 : (1:ℝ) ≤ Cr * (1 + |T|)^(P + Pn) := by
    have h1T : (1:ℝ) ≤ 1 + |T| := by linarith [abs_nonneg T]
    calc (1:ℝ) = 1 * 1 := by norm_num
      _ ≤ Cr * (1 + |T|)^(P + Pn) :=
          mul_le_mul hCr1 (one_le_pow₀ h1T) (by norm_num) (by linarith)
  have hgbound : ∀ z ∈ Metric.sphere c |A+3|, ‖g z‖ ≤ Cr * (1 + |T|)^(P + Pn) := by
    intro z hz
    have hzball : z ∈ Metric.closedBall c (A+3) := by
      rw [Metric.mem_closedBall]
      rw [Metric.mem_sphere] at hz
      rw [hz, abs_of_pos (by linarith : (0:ℝ) < A + 3)]
    have hup := hball T hT z hzball
    rw [hg]
    rw [norm_mul, norm_inv]
    have hE : (0:ℝ) < Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) := Real.exp_pos _
    have hinv : ‖completedDedekindZetaEntire K c‖⁻¹
        ≤ ((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) := by
      rw [inv_le_iff_one_le_mul₀ hHcpos]
      have hstep : cL * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) / (1 + |T|)^Pn
          * (((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4)) = 1 := by
        field_simp
      calc (1:ℝ) = cL * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) / (1 + |T|)^Pn
          * (((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4)) :=
            hstep.symm
        _ ≤ ‖completedDedekindZetaEntire K c‖
            * (((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4)) := by
            refine mul_le_mul_of_nonneg_right hHc (by positivity)
        _ = (((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4))
            * ‖completedDedekindZetaEntire K c‖ := by ring
    calc ‖completedDedekindZetaEntire K c‖⁻¹ * ‖completedDedekindZetaEntire K z‖
        ≤ (((1 + |T|)^Pn / cL) / Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4))
          * (cB * (1 + |T|)^P * Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4)) :=
          mul_le_mul hinv hup (norm_nonneg _) (by positivity)
      _ = cB / cL * (1 + |T|)^(P + Pn) := by
          rw [show P + Pn = Pn + P by ring, pow_add]
          field_simp
          ring
      _ ≤ Cr * (1 + |T|)^(P + Pn) :=
          mul_le_mul_of_nonneg_right (by rw [hCr]; linarith) (by positivity)
  -- Jensen counting for g
  have habs_r : |A + 2| = A + 2 := abs_of_pos hrpos
  have habs_R : |A + 3| = A + 3 := abs_of_pos (by linarith : (0:ℝ) < A + 3)
  have hcount := AnalyticOnNhd.sum_divisor_le
    (c := c) (r := A + 2) (R := A + 3) (M := Cr * (1 + |T|)^(P + Pn)) (f := g)
    (by rw [habs_r]; exact hrpos)
    (by rw [habs_r, habs_R]; exact hrR)
    hM1 hganal (by rw [hgc]; norm_num) hgbound
  -- divisor transfer to H
  have hHmero : MeromorphicOn (completedDedekindZetaEntire K)
      (Metric.closedBall c |A + 2|) := fun z _ =>
    ((differentiable_completedDedekindZetaEntire K).analyticAt z).meromorphicAt
  have hconstmero : MeromorphicOn (fun _ : ℂ => (completedDedekindZetaEntire K c)⁻¹)
      (Metric.closedBall c |A + 2|) := fun z _ =>
    analyticAt_const.meromorphicAt
  have hordc : ∀ z ∈ Metric.closedBall c |A + 2|,
      meromorphicOrderAt (fun _ : ℂ => (completedDedekindZetaEntire K c)⁻¹) z ≠ ⊤ := by
    intro z _
    classical
    rw [meromorphicOrderAt_const, if_neg (inv_ne_zero hHcne)]
    exact WithTop.zero_ne_top
  have hcmem : c ∈ Metric.closedBall c |A + 2| := by
    rw [habs_r]
    exact Metric.mem_closedBall_self hrpos.le
  have hordHc : meromorphicOrderAt (completedDedekindZetaEntire K) c ≠ ⊤ := by
    rw [((differentiable_completedDedekindZetaEntire K).analyticAt c).meromorphicOrderAt_eq]
    have h0 : analyticOrderAt (completedDedekindZetaEntire K) c = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hHcne)
    rw [h0]
    simp
  have hordH : ∀ z ∈ Metric.closedBall c |A + 2|,
      meromorphicOrderAt (completedDedekindZetaEntire K) z ≠ ⊤ := by
    intro z hz
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hHmero
      ((convex_closedBall _ _).isPreconnected) hcmem hz hordHc
  have hdiv : MeromorphicOn.divisor g (Metric.closedBall c |A + 2|)
      = MeromorphicOn.divisor (completedDedekindZetaEntire K)
        (Metric.closedBall c |A + 2|) := by
    have hgdef : g = fun z => (fun _ : ℂ => (completedDedekindZetaEntire K c)⁻¹) z
        * completedDedekindZetaEntire K z := rfl
    rw [hgdef, MeromorphicOn.divisor_fun_mul hconstmero hHmero hordc hordH,
      MeromorphicOn.divisor_const]
    simp
  rw [hdiv] at hcount
  rw [habs_r] at hcount
  refine le_trans hcount ?_
  -- the log-quotient bound
  rw [hgc, norm_one, div_one]
  have h1T : (1:ℝ) ≤ 1 + |T| := by linarith [abs_nonneg T]
  have hL1 : (1:ℝ) ≤ Real.log (2 + |T|) := by
    have he9 : Real.exp 1 ≤ 2 + |T| := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 + |T|) := Real.log_le_log (Real.exp_pos 1) he9
  have hlogM : Real.log (Cr * (1 + |T|)^(P + Pn))
      ≤ (Real.log Cr + (P + Pn + 1)) * Real.log (2 + |T|) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hlog1 : Real.log (1 + |T|) ≤ Real.log (2 + |T|) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlogCr : (0:ℝ) ≤ Real.log Cr := Real.log_nonneg hCr1
    have hPP : (0:ℝ) ≤ ((P + Pn : ℕ) : ℝ) := Nat.cast_nonneg _
    calc Real.log Cr + ((P + Pn : ℕ) : ℝ) * Real.log (1 + |T|)
        ≤ Real.log Cr * Real.log (2 + |T|)
          + ((P + Pn : ℕ) : ℝ) * Real.log (2 + |T|) := by
          have h1 : Real.log Cr ≤ Real.log Cr * Real.log (2 + |T|) := by
            nlinarith
          have h2 : ((P + Pn : ℕ) : ℝ) * Real.log (1 + |T|)
              ≤ ((P + Pn : ℕ) : ℝ) * Real.log (2 + |T|) :=
            mul_le_mul_of_nonneg_left hlog1 hPP
          linarith
      _ ≤ (Real.log Cr + (P + Pn + 1)) * Real.log (2 + |T|) := by
          push_cast
          nlinarith
  calc Real.log (Cr * (1 + |T|)^(P + Pn)) / Real.log ((A+3) / (A+2))
      ≤ ((Real.log Cr + (P + Pn + 1)) * Real.log (2 + |T|))
        / Real.log ((A+3) / (A+2)) := by
        gcongr
    _ = (Real.log Cr + (P + Pn + 1)) / Real.log ((A+3) / (A+2))
        * Real.log (2 + |T|) := by ring

/-- **Two-radius zero-peeling** (A5-ii-b′): peel only the zeros of `H` inside the small
ball `ball c r₁`; the cofactor `h` is analytic on the *large* ball `ball c r₂` and
zero-free on the small ball. This is the shape the Landau/Titchmarsh maximum-principle
argument needs: on spheres of intermediate radius the peeled product is bounded below by
the separation, while `h` is still analytic there. -/
theorem exists_H_two_radius_factorization (c : ℂ) {r₁ r₂ : ℝ} (h12 : r₁ ≤ r₂)
    {w : ℂ} (hw : w ∈ Metric.ball c r₁)
    (hHw : completedDedekindZetaEntire K w ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (Metric.ball c r₂)
      ∧ (∀ z ∈ Metric.ball c r₁, h z ≠ 0)
      ∧ ∀ z ∈ Metric.ball c r₂,
          completedDedekindZetaEntire K z
            = (∏ᶠ u, (z - u) ^ ((MeromorphicOn.divisor (completedDedekindZetaEntire K)
                (Metric.ball c r₁)) u)) * h z := by
  have hsub : Metric.ball c r₁ ⊆ Metric.ball c r₂ := Metric.ball_subset_ball h12
  obtain ⟨g, hganal, hgne, hfac⟩ := exists_H_ball_factorization K c (hsub hw) hHw
  have hHanal : AnalyticOnNhd ℂ (completedDedekindZetaEntire K) Set.univ := fun z _ =>
    (differentiable_completedDedekindZetaEntire K).analyticAt z
  have hm₁ : MeromorphicOn (completedDedekindZetaEntire K) (Metric.ball c r₁) :=
    fun z _ => (hHanal z trivial).meromorphicAt
  have hm₂ : MeromorphicOn (completedDedekindZetaEntire K) (Metric.ball c r₂) :=
    fun z _ => (hHanal z trivial).meromorphicAt
  set D₁ : ℂ → ℤ := fun u => (MeromorphicOn.divisor (completedDedekindZetaEntire K)
    (Metric.ball c r₁)) u with hD₁
  set D₂ : ℂ → ℤ := fun u => (MeromorphicOn.divisor (completedDedekindZetaEntire K)
    (Metric.ball c r₂)) u with hD₂
  -- pointwise comparison of the two divisors
  have hD₁_mem : ∀ u ∈ Metric.ball c r₁, D₁ u = D₂ u := by
    intro u hu
    rw [hD₁, hD₂]
    simp only
    rw [MeromorphicOn.divisor_apply hm₁ hu, MeromorphicOn.divisor_apply hm₂ (hsub hu)]
  have hD₁_zero : ∀ u, u ∉ Metric.ball c r₁ → D₁ u = 0 := by
    intro u hu
    rw [hD₁]
    simp only
    exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
  have hD₁nn : ∀ u, 0 ≤ D₁ u := fun u =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ => hHanal z trivial)) u
  have hD₂nn : ∀ u, 0 ≤ D₂ u := fun u =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ => hHanal z trivial)) u
  -- the annulus exponents
  set dA : ℂ → ℤ := fun u => D₂ u - D₁ u with hdA
  have hdAnn : ∀ u, 0 ≤ dA u := by
    intro u
    rw [hdA]
    by_cases hu : u ∈ Metric.ball c r₁
    · simp [hD₁_mem u hu]
    · simp [hD₁_zero u hu, hD₂nn u]
  have hdA_zero : ∀ u ∈ Metric.ball c r₁, dA u = 0 := by
    intro u hu
    rw [hdA]
    simp [hD₁_mem u hu]
  -- finite supports
  have hfin₁ : (Function.support D₁).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset
      (fun z _ => (hHanal z trivial).meromorphicAt)
      (isCompact_closedBall c r₁) Metric.ball_subset_closedBall
  have hfin₂ : (Function.support D₂).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset
      (fun z _ => (hHanal z trivial).meromorphicAt)
      (isCompact_closedBall c r₂) Metric.ball_subset_closedBall
  have hfinA : (Function.support dA).Finite := by
    refine (hfin₂.union hfin₁).subset ?_
    intro u hu
    rw [Function.mem_support, hdA] at hu
    by_contra hcon
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
    simp [hcon.1, hcon.2] at hu
  -- mulSupport finiteness for the three factor families, at every point
  have hms : ∀ (d : ℂ → ℤ), (Function.support d).Finite → ∀ z : ℂ,
      (Function.mulSupport fun u => (z - u) ^ d u).Finite := by
    intro d hd z
    refine hd.subset ?_
    intro u hu
    rw [Function.mem_mulSupport] at hu
    rw [Function.mem_support]
    intro h0
    rw [h0, zpow_zero] at hu
    exact hu rfl
  -- pointwise product split
  have hsplit : ∀ z : ℂ, (∏ᶠ u, (z - u) ^ D₂ u)
      = (∏ᶠ u, (z - u) ^ D₁ u) * (∏ᶠ u, (z - u) ^ dA u) := by
    intro z
    calc (∏ᶠ u, (z - u) ^ D₂ u)
        = ∏ᶠ u, ((z - u) ^ D₁ u * (z - u) ^ dA u) := by
          refine finprod_congr (fun u => ?_)
          have hexp : D₂ u = D₁ u + dA u := by rw [hdA]; ring
          rw [hexp, zpow_add' (Or.inr (by
            have h1 := hD₁nn u
            have h2 := hdAnn u
            omega))]
      _ = (∏ᶠ u, (z - u) ^ D₁ u) * (∏ᶠ u, (z - u) ^ dA u) :=
          finprod_mul_distrib (hms D₁ hfin₁ z) (hms dA hfinA z)
  -- the cofactor
  refine ⟨fun z => (∏ᶠ u, (z - u) ^ dA u) * g z, ?_, ?_, ?_⟩
  · -- analytic on the large ball
    have heqfun : (fun z => (∏ᶠ u, (z - u) ^ dA u) * g z)
        = fun z => (∏ᶠ u, (· - u) ^ dA u) z * g z := by
      funext z
      rw [Function.FactorizedRational.finprod_eq_fun hfinA]
    rw [heqfun]
    intro z hz
    exact (Function.FactorizedRational.analyticAt (hdAnn z)).mul (hganal z hz)
  · -- zero-free on the small ball
    intro z hz
    refine mul_ne_zero ?_ (hgne z (hsub hz))
    rw [finprod_eq_prod _ (hms dA hfinA z)]
    refine Finset.prod_ne_zero_iff.mpr (fun u hu => ?_)
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport] at hu
    have hdu : dA u ≠ 0 := by
      intro h0
      rw [h0, zpow_zero] at hu
      exact hu rfl
    have huout : u ∉ Metric.ball c r₁ := fun hin => hdu (hdA_zero u hin)
    have hzu : z - u ≠ 0 := sub_ne_zero_of_ne (fun h => huout (h ▸ hz))
    exact zpow_ne_zero _ hzu
  · -- the factorization
    intro z hz
    rw [hfac z hz, hsplit z]
    ring

/-- **Landau's logarithmic-derivative bound** (A5-ii-c, generic form): if `h` is
holomorphic and zero-free on `ball c r` with `‖h‖ ≤ mS` there and `mL ≤ ‖h c‖` at the
center, then `‖h'/h‖ ≤ 32·r·(log(mS/mL) + 1)` on the concentric closed ball of radius
`r - 3/4`. Chain: holomorphic logarithm on the convex ball, Borel–Carathéodory from the
`Re`-bound `log(mS/mL)`, then the Schwarz derivative estimate on quarter-balls. -/
theorem norm_logDeriv_le_of_norm_le {h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 3/4 < r)
    (hd : DifferentiableOn ℂ h (Metric.ball c r))
    (h0 : ∀ z ∈ Metric.ball c r, h z ≠ 0)
    {mS mL : ℝ} (hmL : 0 < mL) (hcL : mL ≤ ‖h c‖)
    (hS : ∀ z ∈ Metric.ball c r, ‖h z‖ ≤ mS) :
    ∀ s ∈ Metric.closedBall c (r - 3/4),
      ‖logDeriv h s‖ ≤ 32 * r * (Real.log (mS/mL) + 1) := by
  have hr0 : (0:ℝ) < r := by linarith
  have hcmem : c ∈ Metric.ball c r := Metric.mem_ball_self hr0
  -- the holomorphic logarithm
  obtain ⟨L, hLd, hLeq⟩ := exists_differentiableOn_log Metric.isOpen_ball
    (convex_ball c r) ⟨c, hcmem⟩ hd h0
  -- the ratio constant
  set M : ℝ := Real.log (mS/mL) + 1 with hM
  have hmS : 0 < mS := lt_of_lt_of_le hmL (le_trans hcL (hS c hcmem))
  have hratio1 : (1:ℝ) ≤ mS/mL := (one_le_div hmL).mpr (le_trans hcL (hS c hcmem))
  have hM1 : (1:ℝ) ≤ M := by
    rw [hM]
    linarith [Real.log_nonneg hratio1]
  have hM0 : (0:ℝ) < M := by linarith
  -- Re (L z - L c) = log ‖h z‖ - log ‖h c‖ ≤ log (mS/mL) ≤ M on the ball
  have hreL : ∀ z ∈ Metric.ball c r, (L z).re = Real.log ‖h z‖ := by
    intro z hz
    have hexp : Complex.exp (L z) = h z := hLeq hz
    have : ‖h z‖ = Real.exp ((L z).re) := by
      rw [← hexp, Complex.norm_exp]
    rw [this, Real.log_exp]
  have hreG : ∀ z ∈ Metric.ball c r, (L z - L c).re ≤ M := by
    intro z hz
    rw [Complex.sub_re, hreL z hz, hreL c hcmem]
    have h1 : Real.log ‖h z‖ ≤ Real.log mS :=
      Real.log_le_log (norm_pos_iff.mpr (h0 z hz)) (hS z hz)
    have h2 : Real.log mL ≤ Real.log ‖h c‖ := Real.log_le_log hmL hcL
    have h3 : Real.log (mS/mL) = Real.log mS - Real.log mL :=
      Real.log_div hmS.ne' hmL.ne'
    rw [hM]
    linarith
  -- Borel–Carathéodory, recentered at the origin
  have hGd : DifferentiableOn ℂ (fun w => L (c + w) - L c) (Metric.ball 0 r) := by
    refine DifferentiableOn.sub_const ?_ _
    refine hLd.comp (differentiable_id.const_add c).differentiableOn ?_
    intro w hw
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hBC : ∀ w ∈ Metric.ball (0:ℂ) r,
      ‖L (c + w) - L c‖ ≤ 2 * M * ‖w‖ / (r - ‖w‖) := by
    intro w hw
    refine Complex.borelCaratheodory_zero hM0 hGd ?_ hr0 hw ?_
    · intro x hx
      simp only [Set.mem_setOf_eq]
      refine hreG (c + x) ?_
      rw [Metric.mem_ball] at hx ⊢
      simpa [dist_eq_norm] using hx
    · simp
  -- uniform bound on the sub-ball of radius r - 1/2
  have hGbound : ∀ z ∈ Metric.ball c (r - 1/2), ‖L z - L c‖ ≤ 4 * M * r := by
    intro z hz
    have hzc : ‖z - c‖ < r - 1/2 := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact hz
    have hw : z - c ∈ Metric.ball (0:ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have h1 := hBC (z - c) hw
    rw [add_sub_cancel] at h1
    refine le_trans h1 ?_
    have hden : (1:ℝ)/2 < r - ‖z - c‖ := by linarith
    calc 2 * M * ‖z - c‖ / (r - ‖z - c‖)
        ≤ 2 * M * r / (r - ‖z - c‖) := by
          gcongr
          linarith
      _ ≤ 2 * M * r / (1/2) := by
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hden.le
      _ = 4 * M * r := by ring
  -- Schwarz derivative estimate on quarter-balls
  intro s hs
  have hsball : s ∈ Metric.ball c r := by
    rw [Metric.mem_closedBall] at hs
    rw [Metric.mem_ball]
    linarith
  have hsub : Metric.ball s (1/4) ⊆ Metric.ball c (r - 1/2) := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    rw [Metric.mem_closedBall] at hs
    calc dist z c ≤ dist z s + dist s c := dist_triangle z s c
      _ < 1/4 + (r - 3/4) := by linarith
      _ = r - 1/2 := by ring
  have hsub2 : Metric.ball s (1/4) ⊆ Metric.ball c r := by
    intro z hz
    have := hsub hz
    rw [Metric.mem_ball] at this ⊢
    linarith
  set G : ℂ → ℂ := fun z => L z - L c with hG
  have hGdiff : DifferentiableOn ℂ G (Metric.ball s (1/4)) :=
    (hLd.mono hsub2).sub_const _
  have hmaps : Set.MapsTo G (Metric.ball s (1/4))
      (Metric.closedBall (G s) (8 * M * r)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 : ‖G z‖ ≤ 4 * M * r := hGbound z (hsub hz)
    have h2 : ‖G s‖ ≤ 4 * M * r := by
      refine hGbound s ?_
      rw [Metric.mem_ball]
      rw [Metric.mem_closedBall] at hs
      linarith
    calc ‖G z - G s‖ ≤ ‖G z‖ + ‖G s‖ := norm_sub_le _ _
      _ ≤ 8 * M * r := by linarith
  have hderiv := Complex.norm_deriv_le_div_of_mapsTo_ball hGdiff hmaps (by norm_num)
  -- identify deriv G with logDeriv h
  have hLds : DifferentiableAt ℂ L s :=
    hLd.differentiableAt (Metric.isOpen_ball.mem_nhds hsball)
  have hderivG : deriv G s = deriv L s := by
    rw [hG]
    simp
  have hlogDeriv : logDeriv h s = deriv L s := by
    have hhs : h s ≠ 0 := h0 s hsball
    have hexps : Complex.exp (L s) = h s := hLeq hsball
    have hev : h =ᶠ[nhds s] fun z => Complex.exp (L z) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hsball] with z hz
      exact (hLeq hz).symm
    rw [logDeriv, Pi.div_apply, hev.deriv_eq]
    rw [deriv_cexp hLds, hexps]
    field_simp
  rw [hlogDeriv, ← hderivG]
  refine le_trans hderiv ?_
  rw [show (8 : ℝ) * M * r / (1/4) = 32 * r * M by ring]

/-- **The Landau cofactor for `H` near height `T`** (A5-ii assembly): there is an
abscissa `A` and a constant `C` such that at every height `|T| ≥ A+5` the completed
zeta factors through the zeros in `ball (A+iT) (A+2)` with a cofactor `h` that is
analytic on `ball (A+iT) (A+3)`, zero-free on `ball (A+iT) (A+2)`, and whose
logarithmic derivative is `O(log(2+|T|))` on the slab ball `closedBall (A+iT) (A+5/4)`
— a ball containing the strip `-1 ≤ Re ≤ 2`, `|Im - T| ≤ 1`. -/
theorem exists_H_landau_cofactor :
    ∃ A : ℝ, 2 ≤ A ∧ ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, A + 5 ≤ |T| →
      ((∑ᶠ u, (MeromorphicOn.divisor (completedDedekindZetaEntire K)
          (Metric.ball ((A : ℂ) + (T : ℂ) * Complex.I) (A + 2))) u : ℤ) : ℝ)
        ≤ C * Real.log (2 + |T|) ∧
      ∃ h : ℂ → ℂ,
        AnalyticOnNhd ℂ h (Metric.ball ((A : ℂ) + (T : ℂ) * Complex.I) (A + 3))
        ∧ (∀ z ∈ Metric.ball ((A : ℂ) + (T : ℂ) * Complex.I) (A + 2), h z ≠ 0)
        ∧ (∀ z ∈ Metric.ball ((A : ℂ) + (T : ℂ) * Complex.I) (A + 3),
            completedDedekindZetaEntire K z
              = (∏ᶠ u, (z - u) ^ ((MeromorphicOn.divisor (completedDedekindZetaEntire K)
                  (Metric.ball ((A : ℂ) + (T : ℂ) * Complex.I) (A + 2))) u)) * h z)
        ∧ ∀ s ∈ Metric.closedBall ((A : ℂ) + (T : ℂ) * Complex.I) (A + 5/4),
            ‖logDeriv h s‖ ≤ C * Real.log (2 + |T|) := by
  obtain ⟨A, hA2, cL, hcL, hlow⟩ := exists_H_center_lower K
  obtain ⟨cB, hcB, P, hsup⟩ := exists_H_ball_sup_big K A hA2
  obtain ⟨Cc, hCc, hcount⟩ := exists_ball_zero_count_big K A hA2 cL hcL hlow
  set n : ℕ := gammaExponent K with hn
  set Pn : ℕ := nrRealPlaces K + nrComplexPlaces K with hPn
  have hlog2A : 0 < Real.log (2*(A+2)) := Real.log_pos (by linarith)
  refine ⟨A, hA2, 32 * (A+2)
    * (|Real.log (cB/cL)| + (P+Pn) + Cc * Real.log (2*(A+2)) + 1) + Cc,
    by positivity, fun T hT => ?_⟩
  set c : ℂ := (A : ℂ) + (T : ℂ) * Complex.I with hcdef
  have hT2 : 2 ≤ |T| := by linarith
  -- center value
  have hHc := hlow T hT2
  have hHcpos : 0 < ‖completedDedekindZetaEntire K c‖ :=
    lt_of_lt_of_le (by positivity) hHc
  have hHcne : completedDedekindZetaEntire K c ≠ 0 := by
    intro h0
    rw [h0] at hHcpos
    simp at hHcpos
  -- the factorization
  have hcmem : c ∈ Metric.ball c (A+2) := Metric.mem_ball_self (by linarith)
  obtain ⟨h, hhanal, hhne, hfac⟩ := exists_H_two_radius_factorization K c
    (show (A+2:ℝ) ≤ A+3 by linarith) hcmem hHcne
  -- divisor data
  have hHanal : ∀ z : ℂ, AnalyticAt ℂ (completedDedekindZetaEntire K) z := fun z =>
    (differentiable_completedDedekindZetaEntire K).analyticAt z
  set D₁ : ℂ → ℤ := fun u => (MeromorphicOn.divisor (completedDedekindZetaEntire K)
    (Metric.ball c (A+2))) u with hD₁
  have hD₁nn : ∀ u, 0 ≤ D₁ u := fun u =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ => hHanal z)) u
  have hfin₁ : (Function.support D₁).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset
      (fun z _ => (hHanal z).meromorphicAt)
      (isCompact_closedBall c (A+2)) Metric.ball_subset_closedBall
  set F : Finset ℂ := hfin₁.toFinset with hF
  set Dnat : ℕ := ∑ u ∈ F, (D₁ u).toNat with hDnatdef
  -- support inside the peel ball
  have hsuppF : ∀ u ∈ F, u ∈ Metric.ball c (A+2) := by
    intro u hu
    exact (MeromorphicOn.divisor (completedDedekindZetaEntire K)
      (Metric.ball c (A+2))).supportWithinDomain (hfin₁.mem_toFinset.mp hu)
  -- pointwise finprod → Finset.prod
  have hP₁ : ∀ z : ℂ, (∏ᶠ u, (z - u) ^ D₁ u) = ∏ u ∈ F, (z - u) ^ D₁ u := by
    intro z
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro u hu
    rw [Function.mem_mulSupport] at hu
    refine hfin₁.mem_toFinset.mpr (Function.mem_support.mpr ?_)
    intro h0
    rw [h0, zpow_zero] at hu
    exact hu rfl
  -- norms of the peel product
  have hQ : ∀ z : ℂ, ‖∏ u ∈ F, (z - u) ^ D₁ u‖ = ∏ u ∈ F, ‖z - u‖^((D₁ u).toNat) := by
    intro z
    rw [norm_prod]
    refine Finset.prod_congr rfl (fun u _ => ?_)
    rw [show D₁ u = ((D₁ u).toNat : ℤ) from (Int.toNat_of_nonneg (hD₁nn u)).symm,
      zpow_natCast, norm_pow, Int.toNat_natCast]
  -- the envelope pieces
  set E : ℝ := Real.exp (-(((n:ℕ) : ℝ) * (π * |T|)) / 4) with hE
  have hEpos : 0 < E := Real.exp_pos _
  set mS : ℝ := cB * (1 + |T|)^P * E * 2^Dnat with hmS
  set mL : ℝ := cL * E / (1 + |T|)^Pn / (A+2)^Dnat with hmL
  have h1T : (0:ℝ) < 1 + |T| := by linarith [abs_nonneg T]
  have hmSpos : 0 < mS := by rw [hmS]; positivity
  have hmLpos : 0 < mL := by rw [hmL]; positivity
  -- sup bound for h on the peel ball, via the maximum principle at radius A+5/2
  have hballs : Metric.ball c (A + 5/2) ⊆ Metric.ball c (A+3) :=
    Metric.ball_subset_ball (by linarith)
  have hcbs : Metric.closedBall c (A + 5/2) ⊆ Metric.ball c (A+3) := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    linarith
  have hclosure : closure (Metric.ball c (A + 5/2)) = Metric.closedBall c (A + 5/2) :=
    closure_ball c (ne_of_gt (by linarith : (0:ℝ) < A + 5/2))
  have hfrontier : frontier (Metric.ball c (A + 5/2)) = Metric.sphere c (A + 5/2) :=
    frontier_ball c (ne_of_gt (by linarith : (0:ℝ) < A + 5/2))
  have hhsup : ∀ z ∈ Metric.ball c (A+2), ‖h z‖ ≤ mS := by
    intro z hz
    have hzcl : z ∈ closure (Metric.ball c (A + 5/2)) := by
      rw [hclosure, Metric.mem_closedBall]
      rw [Metric.mem_ball] at hz
      linarith
    refine Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball ⟨hhanal.differentiableOn.mono hballs, ?_⟩ ?_ hzcl
    · rw [hclosure]
      exact hhanal.continuousOn.mono hcbs
    · intro x hx
      rw [hfrontier, Metric.mem_sphere] at hx
      have hxball : x ∈ Metric.ball c (A+3) := by
        rw [Metric.mem_ball, hx]
        linarith
      have hfacx := hfac x hxball
      rw [hP₁ x] at hfacx
      -- lower bound the peel product on the sphere
      have hlowfac : ((1:ℝ)/2)^Dnat ≤ ‖∏ u ∈ F, (x - u) ^ D₁ u‖ := by
        rw [hQ x]
        have hstep : ∀ u ∈ F, ((1:ℝ)/2)^((D₁ u).toNat) ≤ ‖x - u‖^((D₁ u).toNat) := by
          intro u hu
          refine pow_le_pow_left₀ (by norm_num) ?_ _
          have hd := hsuppF u hu
          rw [Metric.mem_ball] at hd
          rw [← dist_eq_norm]
          have htri := dist_triangle x u c
          have hcomm : dist u c = dist c u := dist_comm u c
          have : dist x u ≥ dist x c - dist u c := by linarith
          rw [hx] at this
          linarith
        calc ((1:ℝ)/2)^Dnat = ∏ u ∈ F, ((1:ℝ)/2)^((D₁ u).toNat) := by
              rw [Finset.prod_pow_eq_pow_sum]
          _ ≤ ∏ u ∈ F, ‖x - u‖^((D₁ u).toNat) :=
              Finset.prod_le_prod (fun u _ => by positivity) hstep
      have hppos : (0:ℝ) < ‖∏ u ∈ F, (x - u) ^ D₁ u‖ :=
        lt_of_lt_of_le (by positivity) hlowfac
      -- upper bound H on the sphere
      have hxcb : x ∈ Metric.closedBall c (A+3) := by
        rw [Metric.mem_closedBall, hx]
        linarith
      have hHx := hsup T hT x hxcb
      -- combine
      have hnorm : ‖completedDedekindZetaEntire K x‖
          = ‖∏ u ∈ F, (x - u) ^ D₁ u‖ * ‖h x‖ := by
        rw [hfacx, norm_mul]
      have hkey : ‖h x‖ * ((1:ℝ)/2)^Dnat ≤ cB * (1 + |T|)^P * E := by
        calc ‖h x‖ * ((1:ℝ)/2)^Dnat
            ≤ ‖h x‖ * ‖∏ u ∈ F, (x - u) ^ D₁ u‖ :=
              mul_le_mul_of_nonneg_left hlowfac (norm_nonneg _)
          _ = ‖completedDedekindZetaEntire K x‖ := by rw [hnorm]; ring
          _ ≤ cB * (1 + |T|)^P * E := hHx
      have hhalfpos : (0:ℝ) < ((1:ℝ)/2)^Dnat := by positivity
      rw [← le_div_iff₀ hhalfpos] at hkey
      refine le_trans hkey (le_of_eq ?_)
      rw [hmS, one_div, inv_pow, div_eq_mul_inv, inv_inv]
  -- center lower bound for h
  have hcball3 : c ∈ Metric.ball c (A+3) := Metric.mem_ball_self (by linarith)
  have hfacc := hfac c hcball3
  rw [hP₁ c] at hfacc
  have hPcne : (∏ u ∈ F, (c - u) ^ D₁ u) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hfacc
    exact hHcne hfacc
  have hPc_ub : ‖∏ u ∈ F, (c - u) ^ D₁ u‖ ≤ (A+2)^Dnat := by
    rw [hQ c]
    have hstep : ∀ u ∈ F, ‖c - u‖^((D₁ u).toNat) ≤ (A+2)^((D₁ u).toNat) := by
      intro u hu
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      have hd := hsuppF u hu
      rw [Metric.mem_ball] at hd
      rw [← dist_eq_norm, dist_comm]
      linarith
    calc ∏ u ∈ F, ‖c - u‖^((D₁ u).toNat)
        ≤ ∏ u ∈ F, (A+2)^((D₁ u).toNat) :=
          Finset.prod_le_prod (fun u _ => by positivity) hstep
      _ = (A+2)^Dnat := by rw [Finset.prod_pow_eq_pow_sum]
  have hhc_lb : mL ≤ ‖h c‖ := by
    have hnormc : ‖completedDedekindZetaEntire K c‖
        = ‖∏ u ∈ F, (c - u) ^ D₁ u‖ * ‖h c‖ := by
      rw [hfacc, norm_mul]
    have hA2pos : (0:ℝ) < (A+2)^Dnat := by positivity
    have hstep : ‖completedDedekindZetaEntire K c‖ ≤ (A+2)^Dnat * ‖h c‖ := by
      rw [hnormc]
      exact mul_le_mul_of_nonneg_right hPc_ub (norm_nonneg _)
    have h1 : ‖completedDedekindZetaEntire K c‖ / (A+2)^Dnat ≤ ‖h c‖ := by
      rw [div_le_iff₀ hA2pos]
      calc ‖completedDedekindZetaEntire K c‖ ≤ (A+2)^Dnat * ‖h c‖ := hstep
        _ = ‖h c‖ * (A+2)^Dnat := by ring
    refine le_trans ?_ h1
    rw [hmL]
    gcongr
  -- the zero count controls Dnat
  have hDle : (Dnat : ℝ) ≤ Cc * Real.log (2 + |T|) := by
    set Dcl : ℂ → ℤ := fun u => (MeromorphicOn.divisor (completedDedekindZetaEntire K)
      (Metric.closedBall c (A+2))) u with hDcl
    have hmcl : MeromorphicOn (completedDedekindZetaEntire K)
        (Metric.closedBall c (A+2)) := fun z _ => (hHanal z).meromorphicAt
    have hm₁ : MeromorphicOn (completedDedekindZetaEntire K)
        (Metric.ball c (A+2)) := fun z _ => (hHanal z).meromorphicAt
    have hfincl : (Function.support Dcl).Finite :=
      MeromorphicOn.divisor_support_finite_of_subset hmcl
        (isCompact_closedBall c (A+2)) subset_rfl
    have hDclnn : ∀ u, 0 ≤ Dcl u := fun u =>
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ => hHanal z)) u
    have hpt : ∀ u, D₁ u ≤ Dcl u := by
      intro u
      by_cases hu : u ∈ Metric.ball c (A+2)
      · rw [hD₁, hDcl]
        simp only
        rw [MeromorphicOn.divisor_apply hm₁ hu,
          MeromorphicOn.divisor_apply hmcl (Metric.ball_subset_closedBall hu)]
      · rw [hD₁]
        simp only
        rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
        exact hDclnn u
    have hFsub : F ⊆ hfincl.toFinset := by
      intro u hu
      have hu' := Function.mem_support.mp (hfin₁.mem_toFinset.mp hu)
      refine hfincl.mem_toFinset.mpr (Function.mem_support.mpr ?_)
      intro h0
      refine hu' (le_antisymm ?_ (hD₁nn u))
      rw [← h0]
      exact hpt u
    have hint : (Dnat : ℤ) ≤ ∑ᶠ u, Dcl u := by
      have e1 : (Dnat : ℤ) = ∑ u ∈ F, D₁ u := by
        rw [hDnatdef]
        push_cast
        refine Finset.sum_congr rfl (fun u _ => Int.toNat_of_nonneg (hD₁nn u))
      have e2 : ∑ u ∈ F, D₁ u = ∑ u ∈ hfincl.toFinset, D₁ u := by
        refine Finset.sum_subset hFsub (fun u _ hu => ?_)
        by_contra h0
        exact hu (hfin₁.mem_toFinset.mpr (Function.mem_support.mpr h0))
      have e3 : ∑ u ∈ hfincl.toFinset, D₁ u ≤ ∑ u ∈ hfincl.toFinset, Dcl u :=
        Finset.sum_le_sum (fun u _ => hpt u)
      have e4 : ∑ u ∈ hfincl.toFinset, Dcl u = ∑ᶠ u, Dcl u :=
        (finsum_eq_sum Dcl hfincl).symm
      rw [e1, e2, ← e4]
      exact e3
    have hcast : ((Dnat : ℤ) : ℝ) ≤ ((∑ᶠ u, Dcl u : ℤ) : ℝ) := by
      exact_mod_cast hint
    have := hcount T hT
    calc (Dnat : ℝ) = ((Dnat : ℤ) : ℝ) := by push_cast; ring
      _ ≤ ((∑ᶠ u, Dcl u : ℤ) : ℝ) := hcast
      _ ≤ Cc * Real.log (2 + |T|) := this
  -- export the open-ball zero count
  have hcount_open : ((∑ᶠ u, D₁ u : ℤ) : ℝ)
      ≤ (32 * (A+2)
        * (|Real.log (cB/cL)| + (P+Pn) + Cc * Real.log (2*(A+2)) + 1) + Cc)
        * Real.log (2 + |T|) := by
    have hfs : (∑ᶠ u, D₁ u : ℤ) = (Dnat : ℤ) := by
      rw [finsum_eq_sum D₁ hfin₁, hDnatdef]
      push_cast
      exact (Finset.sum_congr rfl (fun u _ => (Int.toNat_of_nonneg (hD₁nn u)))).symm
    rw [hfs]
    have hlog0 : (0:ℝ) ≤ Real.log (2 + |T|) := Real.log_nonneg (by linarith [abs_nonneg T])
    have hpad : (0:ℝ) ≤ 32 * (A+2)
        * (|Real.log (cB/cL)| + (P+Pn) + Cc * Real.log (2*(A+2)) + 1) := by positivity
    have h1 : ((Dnat : ℤ) : ℝ) = (Dnat : ℝ) := by push_cast; ring
    rw [h1]
    have hBl : (0:ℝ) ≤ 32 * (A+2)
        * (|Real.log (cB/cL)| + (P+Pn) + Cc * Real.log (2*(A+2)) + 1)
        * Real.log (2 + |T|) := mul_nonneg hpad hlog0
    have hexp : (32 * (A+2)
        * (|Real.log (cB/cL)| + (P+Pn) + Cc * Real.log (2*(A+2)) + 1) + Cc)
        * Real.log (2 + |T|)
        = 32 * (A+2)
          * (|Real.log (cB/cL)| + (P+Pn) + Cc * Real.log (2*(A+2)) + 1)
          * Real.log (2 + |T|) + Cc * Real.log (2 + |T|) := by ring
    rw [hexp]
    linarith [hDle, hBl]
  -- the generic Landau bound
  have hland := norm_logDeriv_le_of_norm_le (h := h) (c := c) (r := A+2)
    (by linarith)
    (hhanal.differentiableOn.mono (Metric.ball_subset_ball (by linarith)))
    hhne hmLpos hhc_lb hhsup
  constructor
  · exact hcount_open
  refine ⟨h, hhanal, hhne, fun z hz => by rw [hfac z hz], fun s hs => ?_⟩
  have hs' : s ∈ Metric.closedBall c ((A+2) - 3/4) := by
    rw [Metric.mem_closedBall] at hs ⊢
    linarith
  refine le_trans (hland s hs') ?_
  -- constant chase: 32(A+2)(log(mS/mL)+1) ≤ C·log(2+|T|)
  set ℓ : ℝ := Real.log (2 + |T|) with hℓ
  have hℓ1 : (1:ℝ) ≤ ℓ := by
    rw [hℓ]
    have he9 : Real.exp 1 ≤ 2 + |T| := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 + |T|) := Real.log_le_log (Real.exp_pos 1) he9
  have hlogdiff : Real.log (mS/mL)
      = Real.log cB - Real.log cL + (P+Pn) * Real.log (1 + |T|)
        + (Dnat : ℝ) * Real.log (2*(A+2)) := by
    rw [Real.log_div hmSpos.ne' hmLpos.ne']
    rw [hmS, hmL]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hEpos.ne',
      Real.log_mul hcB.ne' (by positivity),
      Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity),
      Real.log_mul hcL.ne' hEpos.ne',
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (A+2:ℝ) ≠ 0)]
    ring
  have hlog1T : Real.log (1 + |T|) ≤ ℓ := by
    rw [hℓ]
    exact Real.log_le_log (by linarith) (by linarith)
  have hbound : Real.log (mS/mL) + 1
      ≤ (|Real.log (cB/cL)| + (P+Pn) + Cc * Real.log (2*(A+2)) + 1) * ℓ := by
    rw [hlogdiff]
    have b1 : Real.log cB - Real.log cL ≤ |Real.log (cB/cL)| * ℓ := by
      have h1 : Real.log cB - Real.log cL = Real.log (cB/cL) :=
        (Real.log_div hcB.ne' hcL.ne').symm
      rw [h1]
      calc Real.log (cB/cL) ≤ |Real.log (cB/cL)| := le_abs_self _
        _ = |Real.log (cB/cL)| * 1 := by ring
        _ ≤ |Real.log (cB/cL)| * ℓ :=
            mul_le_mul_of_nonneg_left hℓ1 (abs_nonneg _)
    have b2 : ((P+Pn : ℕ) : ℝ) * Real.log (1 + |T|) ≤ ((P+Pn : ℕ) : ℝ) * ℓ :=
      mul_le_mul_of_nonneg_left hlog1T (Nat.cast_nonneg _)
    have b3 : (Dnat : ℝ) * Real.log (2*(A+2)) ≤ Cc * Real.log (2*(A+2)) * ℓ := by
      calc (Dnat : ℝ) * Real.log (2*(A+2))
          ≤ (Cc * ℓ) * Real.log (2*(A+2)) :=
            mul_le_mul_of_nonneg_right hDle hlog2A.le
        _ = Cc * Real.log (2*(A+2)) * ℓ := by ring
    have b4 : (1:ℝ) ≤ 1 * ℓ := by linarith
    push_cast at b2
    rw [add_mul, add_mul, add_mul]
    linarith [b1, b2, b3, b4]
  calc 32 * (A+2) * (Real.log (mS/mL) + 1)
      ≤ 32 * (A+2) * ((|Real.log (cB/cL)| + (P+Pn) + Cc * Real.log (2*(A+2)) + 1) * ℓ) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 32 * (A+2) * (|Real.log (cB/cL)| + (P+Pn) + Cc * Real.log (2*(A+2)) + 1) * ℓ := by
        ring
    _ ≤ (32 * (A+2) * (|Real.log (cB/cL)| + (P+Pn) + Cc * Real.log (2*(A+2)) + 1) + Cc)
        * ℓ := by
        rw [add_mul]
        have h1 : (0:ℝ) ≤ Cc * ℓ := mul_nonneg hCc.le (by linarith)
        linarith

/-- **AC-A5: Landau local partial fractions for the completed Dedekind zeta.**
There are an abscissa `A` and a constant `C` such that for every height `|T| ≥ A+5`
and every non-zero point `s` of the slab ball `closedBall (A+iT) (A+5/4)` — which
contains the strip `-1 ≤ Re s ≤ 2`, `|Im s - T| ≤ 1` — the logarithmic derivative
of `H = completedDedekindZetaEntire` equals the sum of `m_ρ/(s-ρ)` over the zeros
`ρ` in `ball (A+iT) (A+2)` (with multiplicity, encoded by the divisor), up to an
error of at most `C·log(2+|T|)`. This is the workhorse for the explicit-formula
contour estimates on horizontal segments. -/
theorem exists_logDeriv_partial_fractions :
    ∃ A : ℝ, 2 ≤ A ∧ ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, A + 5 ≤ |T| →
      ((∑ᶠ u, (MeromorphicOn.divisor (completedDedekindZetaEntire K)
          (Metric.ball ((A : ℂ) + (T : ℂ) * Complex.I) (A + 2))) u : ℤ) : ℝ)
        ≤ C * Real.log (2 + |T|) ∧
      ∀ s ∈ Metric.closedBall ((A : ℂ) + (T : ℂ) * Complex.I) (A + 5/4),
        completedDedekindZetaEntire K s ≠ 0 →
        ‖logDeriv (completedDedekindZetaEntire K) s
            - ∑ᶠ u, (((MeromorphicOn.divisor (completedDedekindZetaEntire K)
                (Metric.ball ((A : ℂ) + (T : ℂ) * Complex.I) (A + 2))) u : ℂ)) / (s - u)‖
          ≤ C * Real.log (2 + |T|) := by
  obtain ⟨A, hA2, C, hC, hmain⟩ := exists_H_landau_cofactor K
  refine ⟨A, hA2, C, hC, fun T hT => ⟨(hmain T hT).1, fun s hs hHs => ?_⟩⟩
  obtain ⟨h, hhanal, hhne, hfac, hbound⟩ := (hmain T hT).2
  set c : ℂ := (A : ℂ) + (T : ℂ) * Complex.I with hcdef
  have hs2 : s ∈ Metric.ball c (A+2) := by
    rw [Metric.mem_closedBall] at hs
    rw [Metric.mem_ball]
    linarith
  have hs3 : s ∈ Metric.ball c (A+3) := by
    rw [Metric.mem_ball] at hs2 ⊢
    linarith
  -- divisor data
  have hHanal : ∀ z : ℂ, AnalyticAt ℂ (completedDedekindZetaEntire K) z := fun z =>
    (differentiable_completedDedekindZetaEntire K).analyticAt z
  set D₁ : ℂ → ℤ := fun u => (MeromorphicOn.divisor (completedDedekindZetaEntire K)
    (Metric.ball c (A+2))) u with hD₁
  have hD₁nn : ∀ u, 0 ≤ D₁ u := fun u =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ => hHanal z)) u
  have hfin₁ : (Function.support D₁).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset
      (fun z _ => (hHanal z).meromorphicAt)
      (isCompact_closedBall c (A+2)) Metric.ball_subset_closedBall
  set F : Finset ℂ := hfin₁.toFinset with hF
  have hP₁ : ∀ z : ℂ, (∏ᶠ u, (z - u) ^ D₁ u) = ∏ u ∈ F, (z - u) ^ D₁ u := by
    intro z
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro u hu
    rw [Function.mem_mulSupport] at hu
    refine hfin₁.mem_toFinset.mpr (Function.mem_support.mpr ?_)
    intro h0
    rw [h0, zpow_zero] at hu
    exact hu rfl
  -- nonvanishing of the peel product at s
  have hfacs := hfac s hs3
  rw [hP₁ s] at hfacs
  have hPs_ne : (∏ u ∈ F, (s - u) ^ D₁ u) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hfacs
    exact hHs hfacs
  have hfactor_ne : ∀ u ∈ F, (s - u) ^ D₁ u ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hPs_ne
  have hsu_ne : ∀ u ∈ F, s - u ≠ 0 := by
    intro u hu h0
    refine hfactor_ne u hu ?_
    rw [h0]
    refine zero_zpow _ ?_
    exact Function.mem_support.mp (hfin₁.mem_toFinset.mp hu)
  -- logDeriv H = logDeriv (peel) + logDeriv h at s
  have hHev : completedDedekindZetaEntire K
      =ᶠ[nhds s] fun z => (∏ u ∈ F, (z - u) ^ D₁ u) * h z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hs3] with z hz
    rw [hfac z hz, hP₁ z]
  have hpolydiff : DifferentiableAt ℂ (fun z => ∏ u ∈ F, (z - u) ^ D₁ u) s := by
    refine DifferentiableAt.fun_finsetProd (fun u _ => ?_)
    exact (differentiableAt_id.sub_const u).zpow (Or.inr (hD₁nn u))
  have hld : logDeriv (completedDedekindZetaEntire K) s
      = logDeriv (fun z => (∏ u ∈ F, (z - u) ^ D₁ u) * h z) s := by
    rw [logDeriv, logDeriv, Pi.div_apply, Pi.div_apply, hHev.deriv_eq, hHev.eq_of_nhds]
  have hhdiff : DifferentiableAt ℂ h s :=
    (hhanal s hs3).differentiableAt
  have hldmul : logDeriv (fun z => (∏ u ∈ F, (z - u) ^ D₁ u) * h z) s
      = logDeriv (fun z => ∏ u ∈ F, (z - u) ^ D₁ u) s + logDeriv h s :=
    logDeriv_mul s hPs_ne (hhne s hs2) hpolydiff hhdiff
  -- the peel product's logarithmic derivative is the partial-fraction sum
  have hldprod : logDeriv (fun z => ∏ u ∈ F, (z - u) ^ D₁ u) s
      = ∑ u ∈ F, (D₁ u : ℂ) / (s - u) := by
    have h1 : logDeriv (fun z => ∏ u ∈ F, (fun w : ℂ => w - u) z ^ D₁ u) s
        = ∑ u ∈ F, logDeriv (fun z => (fun w : ℂ => w - u) z ^ D₁ u) s := by
      refine logDeriv_prod (fun u hu => hfactor_ne u hu) (fun u hu => ?_)
      exact (differentiableAt_id.sub_const u).zpow (Or.inr (hD₁nn u))
    refine Eq.trans h1 ?_
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have h2 : logDeriv (fun z : ℂ => (z - u) ^ D₁ u) s
        = (D₁ u : ℂ) * logDeriv (fun z : ℂ => z - u) s :=
      logDeriv_fun_zpow (differentiableAt_id.sub_const u) _
    have h3 : logDeriv (fun z : ℂ => z - u) s = 1 / (s - u) := by
      rw [logDeriv, Pi.div_apply]
      simp
    rw [h2, h3, mul_one_div]
  -- fold the Finset sum back into the statement's finsum
  have hfs : (∑ᶠ u, ((D₁ u : ℂ)) / (s - u)) = ∑ u ∈ F, (D₁ u : ℂ) / (s - u) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    refine hfin₁.mem_toFinset.mpr (Function.mem_support.mpr ?_)
    intro h0
    rw [h0] at hu
    simp at hu
  calc ‖logDeriv (completedDedekindZetaEntire K) s
        - ∑ᶠ u, ((D₁ u : ℂ)) / (s - u)‖
      = ‖(∑ u ∈ F, (D₁ u : ℂ) / (s - u) + logDeriv h s)
        - ∑ u ∈ F, (D₁ u : ℂ) / (s - u)‖ := by
        rw [hld, hldmul, hldprod, hfs]
    _ = ‖logDeriv h s‖ := by rw [add_sub_cancel_left]
    _ ≤ C * Real.log (2 + |T|) := hbound s hs

/-- One-step downward recurrence in norm: `‖Γ(z)‖ = ‖Γ(z+1)‖/‖z‖` off the poles. -/
theorem norm_Gamma_eq_norm_Gamma_add_one_div {z : ℂ} (hz : z ≠ 0) :
    ‖Complex.Gamma z‖ = ‖Complex.Gamma (z + 1)‖ / ‖z‖ := by
  rw [Complex.Gamma_add_one z hz, norm_mul]
  field_simp [norm_ne_zero_iff.mpr hz]

/-- σ-uniform decaying Γ-upper on the window `-2 ≤ σ ≤ 3`, `|t| ≥ 1` (the wide window
needed for unit balls around the explicit-formula contour). Left of `Re = -1/2` the
recurrence `Γ(z) = Γ(z+1)/z` steps back into the reflected strip, and `‖z‖ ≥ |t| ≥ 1`
only shrinks the bound. -/
theorem exists_norm_Gamma_le_window :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ, ∀ σ t : ℝ, -2 ≤ σ → σ ≤ 3 → 1 ≤ |t| →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|)^P * Real.exp (-(π * |t|) / 2) := by
  obtain ⟨Cr, hCr, Pr, hright⟩ := exists_norm_Gamma_le_range 3
  refine ⟨Cr + 3/2 * Real.sqrt (12 * π), by positivity, Pr + 1, fun σ t hσl hσr ht => ?_⟩
  have h1t : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have htne : t ≠ 0 := by
    intro h0
    rw [h0] at ht
    norm_num at ht
  -- generic nonvanishing of horizontal translates
  have hzne : ∀ a : ℝ, ((a : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro a h0
    have := congrArg Complex.im h0
    simp at this
    exact htne this
  have hznorm : ∀ a : ℝ, (1:ℝ) ≤ ‖(a : ℂ) + (t : ℂ) * Complex.I‖ := by
    intro a
    calc (1:ℝ) ≤ |t| := ht
      _ = |((a : ℂ) + (t : ℂ) * Complex.I).im| := by simp
      _ ≤ ‖(a : ℂ) + (t : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _
  -- the left-strip bound, packaged
  have hleft : ∀ a : ℝ, -(1/2) ≤ a → a ≤ 1/2 →
      ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ 3/2 * Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 2) := by
    intro a ha1 ha2
    refine le_trans (norm_Gamma_le_mul_exp_left ha1 ha2 ht) ?_
    have hb : ‖((a + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤ (3/2) * (1 + |t|) := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have : |a + 1| ≤ 3/2 := by
        rw [abs_le]
        constructor <;> linarith
      nlinarith [abs_nonneg t]
    calc Real.sqrt (12 * π) * ‖((a + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖
        * Real.exp (-(π * |t|) / 2)
        ≤ Real.sqrt (12 * π) * ((3/2) * (1 + |t|)) * Real.exp (-(π * |t|) / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 3/2 * Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 2) := by ring
  -- common final comparison
  have hpad : ∀ X : ℝ,
      (X ≤ Cr * (1 + |t|)^Pr * Real.exp (-(π * |t|) / 2)
        ∨ X ≤ 3/2 * Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 2)) →
      X ≤ (Cr + 3/2 * Real.sqrt (12 * π)) * (1 + |t|)^(Pr + 1)
        * Real.exp (-(π * |t|) / 2) := by
    intro X hcase
    have hp1 : (1 + |t|)^Pr ≤ (1 + |t|)^(Pr + 1) := pow_le_pow_right₀ h1t (by omega)
    have hp2 : (1 + |t|)^1 ≤ (1 + |t|)^(Pr + 1) := pow_le_pow_right₀ h1t (by omega)
    rcases hcase with hc | hc
    · refine le_trans hc ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine mul_le_mul (le_add_of_nonneg_right (by positivity)) hp1
        (by positivity) (by positivity)
    · refine le_trans hc ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (3/2 : ℝ) * Real.sqrt (12 * π) * (1 + |t|)
          = (3/2 * Real.sqrt (12 * π)) * (1 + |t|)^1 := by ring
        _ ≤ (Cr + 3/2 * Real.sqrt (12 * π)) * (1 + |t|)^(Pr + 1) :=
            mul_le_mul (le_add_of_nonneg_left hCr.le) hp2
              (by positivity) (by positivity)
  refine hpad _ ?_
  -- case split on σ
  rcases le_or_gt (1/2 : ℝ) σ with hc1 | hc1
  · exact Or.inl (hright σ t hc1 hσr ht)
  rcases le_or_gt (-(1/2) : ℝ) σ with hc2 | hc2
  · exact Or.inr (hleft σ hc2 hc1.le)
  rcases le_or_gt (-(3/2) : ℝ) σ with hc3 | hc3
  · -- one step down
    refine Or.inr ?_
    rw [norm_Gamma_eq_norm_Gamma_add_one_div (hzne σ)]
    have hcast : ((σ : ℂ) + (t : ℂ) * Complex.I) + 1
        = ((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [hcast]
    have hb := hleft (σ + 1) (by linarith) (by linarith)
    calc ‖Complex.Gamma (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖
        ≤ ‖Complex.Gamma (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ / 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (hznorm σ)
      _ = ‖Complex.Gamma (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by ring
      _ ≤ 3/2 * Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 2) := hb
  · -- two steps down
    refine Or.inr ?_
    rw [norm_Gamma_eq_norm_Gamma_add_one_div (hzne σ)]
    have hcast : ((σ : ℂ) + (t : ℂ) * Complex.I) + 1
        = ((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [hcast, norm_Gamma_eq_norm_Gamma_add_one_div (hzne (σ + 1))]
    have hcast2 : (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + 1
        = ((σ + 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [hcast2]
    have hb := hleft (σ + 2) (by linarith) (by linarith)
    calc ‖Complex.Gamma (((σ + 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          / ‖((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖
          / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖
        ≤ ‖Complex.Gamma (((σ + 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          / ‖((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ / 1 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) (hznorm σ)
      _ = ‖Complex.Gamma (((σ + 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          / ‖((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ := by ring
      _ ≤ ‖Complex.Gamma (((σ + 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ / 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (hznorm (σ + 1))
      _ = ‖Complex.Gamma (((σ + 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by ring
      _ ≤ 3/2 * Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 2) := hb

/-- σ-uniform Γ-lower on the window `-1 ≤ σ ≤ 2`, `|t| ≥ 1`, with the matching
envelope: `‖Γ(σ+it)‖ ≥ c·e^{-π|t|/2}/(1+|t|)³`. Downward steps divide by at most
`(1+|t|)` each; the base strip and one upward recurrence cover `σ ∈ [1/2, 2]`. -/
theorem exists_le_norm_Gamma_window :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 2 → 1 ≤ |t| →
      c * Real.exp (-(π * |t|) / 2) / (1 + |t|)^3
        ≤ ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set c₀ : ℝ := π / (Real.sqrt (12 * π) * (3/2)) with hc₀
  have hc₀pos : 0 < c₀ := by rw [hc₀]; positivity
  refine ⟨c₀, hc₀pos, fun σ t hσl hσr ht => ?_⟩
  have h1t : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h1tpos : (0:ℝ) < 1 + |t| := by linarith
  have hEpos : (0:ℝ) < Real.exp (-(π * |t|) / 2) := Real.exp_pos _
  have htne : t ≠ 0 := by
    intro h0
    rw [h0] at ht
    norm_num at ht
  have hzne : ∀ a : ℝ, ((a : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro a h0
    have := congrArg Complex.im h0
    simp at this
    exact htne this
  -- the packaged base lower bound: uniform denominator (3/2)(1+|t|) for 1/2 ≤ a ≤ 3/2
  have hbase : ∀ a : ℝ, 1/2 ≤ a → a ≤ 3/2 →
      c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)
        ≤ ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ := by
    intro a ha1 ha2
    refine le_trans ?_ (le_norm_Gamma_base ha1 ha2 ht)
    have hden : ‖((2 - a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖ ≤ (3/2) * (1 + |t|) := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
      have : |2 - a| ≤ 3/2 := by
        rw [abs_le]
        constructor <;> linarith
      nlinarith [abs_nonneg t]
    have hdenpos : (0:ℝ) < ‖((2 - a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖ := by
      refine norm_pos_iff.mpr ?_
      intro h0
      have := congrArg Complex.im h0
      simp at this
      exact htne this
    have hkey : c₀ / (1 + |t|)
        ≤ π / (Real.sqrt (12 * π) * ‖((2 - a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖) := by
      rw [hc₀, div_div]
      refine div_le_div_of_nonneg_left Real.pi_pos.le
        (mul_pos (by positivity) hdenpos) ?_
      calc Real.sqrt (12 * π) * ‖((2 - a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖
          ≤ Real.sqrt (12 * π) * ((3/2) * (1 + |t|)) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
        _ = Real.sqrt (12 * π) * (3/2) * (1 + |t|) := by ring
    calc c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)
        = c₀ / (1 + |t|) * Real.exp (-(π * |t|) / 2) := by ring
      _ ≤ π / (Real.sqrt (12 * π) * ‖((2 - a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖)
          * Real.exp (-(π * |t|) / 2) :=
          mul_le_mul_of_nonneg_right hkey hEpos.le
  -- the packaged base+1 lower bound for 3/2 < a ≤ 2
  have hbase1 : ∀ a : ℝ, 3/2 < a → a ≤ 2 →
      c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)
        ≤ ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ := by
    intro a ha1 ha2
    have hb := le_norm_Gamma_base_add_nat (σ := a - 1) (t := t)
      (by linarith) (by linarith) ht 1
    have hcast : ((a - 1 + (1:ℕ) : ℝ) : ℂ) = (a : ℂ) := by push_cast; ring
    rw [hcast] at hb
    refine le_trans ?_ hb
    have hden : ‖((2 - (a-1) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖
        ≤ (3/2) * (1 + |t|) := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
      have : |2 - (a-1)| ≤ 3/2 := by
        rw [abs_le]
        constructor <;> linarith
      nlinarith [abs_nonneg t]
    have hdenpos : (0:ℝ) < ‖((2 - (a-1) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖ := by
      refine norm_pos_iff.mpr ?_
      intro h0
      have := congrArg Complex.im h0
      simp at this
      exact htne this
    have hkey : c₀ / (1 + |t|)
        ≤ π / (Real.sqrt (12 * π)
          * ‖((2 - (a-1) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖) := by
      rw [hc₀, div_div]
      refine div_le_div_of_nonneg_left Real.pi_pos.le
        (mul_pos (by positivity) hdenpos) ?_
      calc Real.sqrt (12 * π) * ‖((2 - (a-1) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖
          ≤ Real.sqrt (12 * π) * ((3/2) * (1 + |t|)) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
        _ = Real.sqrt (12 * π) * (3/2) * (1 + |t|) := by ring
    calc c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)
        = c₀ / (1 + |t|) * Real.exp (-(π * |t|) / 2) := by ring
      _ ≤ π / (Real.sqrt (12 * π)
          * ‖((2 - (a-1) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖)
          * Real.exp (-(π * |t|) / 2) :=
          mul_le_mul_of_nonneg_right hkey hEpos.le
  -- norms of the translates from above
  have hupnorm : ∀ a : ℝ, |a| ≤ 1 → ‖(a : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + |t| := by
    intro a ha
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  -- the drop-one-power comparison
  have hdrop : c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)^3
      ≤ c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|) := by
    refine div_le_div_of_nonneg_left (by positivity) h1tpos ?_
    calc (1 + |t|) = (1 + |t|)^1 := by ring
      _ ≤ (1 + |t|)^3 := pow_le_pow_right₀ h1t (by omega)
  rcases le_or_gt (1/2 : ℝ) σ with hc1 | hc1
  · rcases le_or_gt σ (3/2 : ℝ) with hc1' | hc1'
    · exact le_trans hdrop (hbase σ hc1 hc1')
    · exact le_trans hdrop (hbase1 σ hc1' hσr)
  rcases le_or_gt (-(1/2) : ℝ) σ with hc2 | hc2
  · -- one step down: ‖Γ(z)‖ = ‖Γ(z+1)‖/‖z‖ ≥ base(σ+1)/(1+|t|)
    rw [norm_Gamma_eq_norm_Gamma_add_one_div (hzne σ)]
    have hcast : ((σ : ℂ) + (t : ℂ) * Complex.I) + 1
        = ((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [hcast]
    have hb := hbase (σ + 1) (by linarith) (by linarith)
    have hzn : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + |t| :=
      hupnorm σ (by rw [abs_le]; constructor <;> linarith)
    have hznpos : (0:ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
      norm_pos_iff.mpr (hzne σ)
    calc c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)^3
        = (c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)) / (1 + |t|)^2 := by
          rw [show ((1:ℝ) + |t|)^3 = (1 + |t|) * (1 + |t|)^2 by ring, ← div_div]
      _ ≤ (c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)) / (1 + |t|) := by
          refine div_le_div_of_nonneg_left (by positivity) h1tpos ?_
          calc (1 + |t|) = (1 + |t|)^1 := by ring
            _ ≤ (1 + |t|)^2 := pow_le_pow_right₀ h1t (by omega)
      _ ≤ ‖Complex.Gamma (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ / (1 + |t|) := by
          gcongr
      _ ≤ ‖Complex.Gamma (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
          gcongr
  · -- two steps down
    rw [norm_Gamma_eq_norm_Gamma_add_one_div (hzne σ)]
    have hcast : ((σ : ℂ) + (t : ℂ) * Complex.I) + 1
        = ((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [hcast, norm_Gamma_eq_norm_Gamma_add_one_div (hzne (σ + 1))]
    have hcast2 : (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + 1
        = ((σ + 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [hcast2]
    have hb := hbase (σ + 2) (by linarith) (by linarith)
    have hzn : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + |t| :=
      hupnorm σ (by rw [abs_le]; constructor <;> linarith)
    have hzn1 : ‖((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + |t| :=
      hupnorm (σ + 1) (by rw [abs_le]; constructor <;> linarith)
    have hznpos : (0:ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
      norm_pos_iff.mpr (hzne σ)
    have hzn1pos : (0:ℝ) < ‖((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ :=
      norm_pos_iff.mpr (hzne (σ + 1))
    calc c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)^3
        = ((c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)) / (1 + |t|)) / (1 + |t|) := by
          rw [show ((1:ℝ) + |t|)^3 = (1 + |t|) * (1 + |t|) * (1 + |t|) by ring,
            ← div_div, ← div_div]
      _ ≤ ((c₀ * Real.exp (-(π * |t|) / 2) / (1 + |t|)) / (1 + |t|))
          / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
          gcongr
      _ ≤ (‖Complex.Gamma (((σ + 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ / (1 + |t|))
          / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
          gcongr
      _ ≤ (‖Complex.Gamma (((σ + 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          / ‖((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖)
          / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
          gcongr

/-- **AC-A6: vertical digamma bound.** On the contour window `-1 ≤ σ ≤ 2`, `|t| ≥ 2`,
the digamma function satisfies `‖ψ(σ+it)‖ ≤ C·log(2+|t|)`. Landau's lemma applied to
`Γ` on the unit ball around `σ+it`: the window sup and center bounds have matching
envelopes `e^{-π|t'|/2}`, so the log-ratio is `O(log(2+|t|))`. -/
theorem exists_norm_digamma_le :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 2 → 2 ≤ |t| →
      ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨Cu, hCu, Pu, hup⟩ := exists_norm_Gamma_le_window
  obtain ⟨cl, hcl, hlow⟩ := exists_le_norm_Gamma_window
  refine ⟨32 * (|Real.log (Cu * 2^Pu * Real.exp (π/2) / cl)| + (Pu + 3) + 1),
    by positivity, fun σ t hσl hσr ht => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have h1t : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  -- points of the unit ball: coordinates
  have hball_re : ∀ z ∈ Metric.ball s 1, -2 ≤ z.re ∧ z.re ≤ 3 := by
    intro z hz
    rw [Metric.mem_ball] at hz
    have h1 : |(z - s).re| ≤ dist z s := by
      rw [dist_eq_norm]
      exact Complex.abs_re_le_norm _
    have h2 : (z - s).re = z.re - σ := by simp [hs]
    rw [h2] at h1
    have := abs_le.mp (le_trans h1 hz.le)
    constructor <;> linarith [this.1, this.2]
  have hball_im : ∀ z ∈ Metric.ball s 1, 1 ≤ |z.im| ∧ |t| - 1 ≤ |z.im|
      ∧ |z.im| ≤ |t| + 1 := by
    intro z hz
    rw [Metric.mem_ball] at hz
    have h1 : |(z - s).im| ≤ dist z s := by
      rw [dist_eq_norm]
      exact Complex.abs_im_le_norm _
    have h2 : (z - s).im = z.im - t := by simp [hs]
    rw [h2] at h1
    have h3 : |z.im - t| ≤ 1 := le_trans h1 hz.le
    have h4 : |t| - |z.im| ≤ |z.im - t| := by
      calc |t| - |z.im| ≤ |t - z.im| := abs_sub_abs_le_abs_sub t z.im
        _ = |z.im - t| := abs_sub_comm t z.im
    have h5 : |z.im| - |t| ≤ |z.im - t| := abs_sub_abs_le_abs_sub z.im t
    refine ⟨by linarith, by linarith, by linarith⟩
  -- no poles in the ball
  have hne_neg : ∀ z ∈ Metric.ball s 1, ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro z hz m h0
    have him := (hball_im z hz).1
    rw [h0] at him
    simp only [Complex.neg_im, Complex.natCast_im, neg_zero, abs_zero] at him
    linarith
  -- Γ is differentiable and zero-free on the ball
  have hd : DifferentiableOn ℂ Complex.Gamma (Metric.ball s 1) := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (hne_neg z hz)).differentiableWithinAt
  have h0 : ∀ z ∈ Metric.ball s 1, Complex.Gamma z ≠ 0 := by
    intro z hz
    exact Complex.Gamma_ne_zero (hne_neg z hz)
  -- envelope pieces
  set E : ℝ := Real.exp (-(π * |t|) / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  set mS : ℝ := Cu * 2^Pu * Real.exp (π/2) * (1 + |t|)^Pu * E with hmS
  set mL : ℝ := cl * E / (1 + |t|)^3 with hmL
  have hmSpos : 0 < mS := by rw [hmS]; positivity
  have hmLpos : 0 < mL := by rw [hmL]; positivity
  -- sup bound on the ball
  have hS : ∀ z ∈ Metric.ball s 1, ‖Complex.Gamma z‖ ≤ mS := by
    intro z hz
    obtain ⟨hre1, hre2⟩ := hball_re z hz
    obtain ⟨him1, him2, him3⟩ := hball_im z hz
    have hzeq : z = ((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := by
      rw [Complex.re_add_im]
    have hb := hup z.re z.im hre1 hre2 him1
    rw [← hzeq] at hb
    refine le_trans hb ?_
    rw [hmS]
    have he1 : Real.exp (-(π * |z.im|) / 2) ≤ Real.exp (π/2) * E := by
      rw [hE, ← Real.exp_add, Real.exp_le_exp]
      have hπ := Real.pi_pos
      nlinarith
    have hp1 : (1 + |z.im|)^Pu ≤ (2 + |t|)^Pu := by
      refine pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) (by linarith) _
    have hp2 : ((2:ℝ) + |t|)^Pu ≤ (2 * (1 + |t|))^Pu := by
      refine pow_le_pow_left₀ (by linarith) (by linarith) _
    calc Cu * (1 + |z.im|)^Pu * Real.exp (-(π * |z.im|) / 2)
        ≤ Cu * ((2 * (1 + |t|))^Pu) * (Real.exp (π/2) * E) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hp1 hp2) hCu.le)
            he1 (by positivity) (by positivity)
      _ = Cu * 2^Pu * Real.exp (π/2) * (1 + |t|)^Pu * E := by
          rw [mul_pow]
          ring
  -- center lower bound
  have hcL : mL ≤ ‖Complex.Gamma s‖ := by
    rw [hmL, hE]
    exact hlow σ t hσl hσr (by linarith)
  -- Landau
  have hland := norm_logDeriv_le_of_norm_le (h := Complex.Gamma) (c := s) (r := 1)
    (by norm_num) hd h0 hmLpos hcL hS
  have hs_self : s ∈ Metric.closedBall s (1 - 3/4) := by
    rw [Metric.mem_closedBall, dist_self]
    norm_num
  have hmain := hland s hs_self
  -- identify digamma with logDeriv Γ
  rw [show Complex.digamma = logDeriv Complex.Gamma from Complex.digamma_def]
  refine le_trans hmain ?_
  -- constant chase
  set ℓ : ℝ := Real.log (2 + |t|) with hℓ
  have hℓ1 : (1:ℝ) ≤ ℓ := by
    rw [hℓ]
    have he9 : Real.exp 1 ≤ 2 + |t| := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 + |t|) := Real.log_le_log (Real.exp_pos 1) he9
  have e1 : Real.log mS
      = Real.log (Cu * 2^Pu) + π/2 + (Pu : ℝ) * Real.log (1 + |t|) + Real.log E := by
    rw [hmS, Real.log_mul (by positivity) hEpos.ne',
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_exp, Real.log_pow]
  have e2 : Real.log mL
      = Real.log cl + Real.log E - 3 * Real.log (1 + |t|) := by
    rw [hmL, Real.log_div (by positivity) (by positivity),
      Real.log_mul hcl.ne' hEpos.ne', Real.log_pow]
    push_cast
    ring
  have e3 : Real.log (Cu * 2^Pu * Real.exp (π/2) / cl)
      = Real.log (Cu * 2^Pu) + π/2 - Real.log cl := by
    rw [Real.log_div (by positivity) hcl.ne',
      Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have hratio : Real.log (mS/mL)
      = Real.log (Cu * 2^Pu * Real.exp (π/2) / cl) + (Pu + 3) * Real.log (1 + |t|) := by
    rw [Real.log_div hmSpos.ne' hmLpos.ne', e1, e2, e3]
    ring
  have hlog1T : Real.log (1 + |t|) ≤ ℓ := by
    rw [hℓ]
    exact Real.log_le_log (by linarith) (by linarith)
  have hfinal : Real.log (mS/mL) + 1
      ≤ (|Real.log (Cu * 2^Pu * Real.exp (π/2) / cl)| + (Pu + 3) + 1) * ℓ := by
    rw [hratio]
    have b1 : Real.log (Cu * 2^Pu * Real.exp (π/2) / cl)
        ≤ |Real.log (Cu * 2^Pu * Real.exp (π/2) / cl)| * ℓ := by
      calc Real.log (Cu * 2^Pu * Real.exp (π/2) / cl)
          ≤ |Real.log (Cu * 2^Pu * Real.exp (π/2) / cl)| := le_abs_self _
        _ = |Real.log (Cu * 2^Pu * Real.exp (π/2) / cl)| * 1 := by ring
        _ ≤ |Real.log (Cu * 2^Pu * Real.exp (π/2) / cl)| * ℓ :=
            mul_le_mul_of_nonneg_left hℓ1 (abs_nonneg _)
    have b2 : ((Pu + 3 : ℕ) : ℝ) * Real.log (1 + |t|) ≤ ((Pu + 3 : ℕ) : ℝ) * ℓ :=
      mul_le_mul_of_nonneg_left hlog1T (Nat.cast_nonneg _)
    have b3 : (1:ℝ) ≤ 1 * ℓ := by linarith
    push_cast at b2
    nlinarith [b1, b2, b3]
  calc 32 * 1 * (Real.log (mS/mL) + 1)
      ≤ 32 * 1 * ((|Real.log (Cu * 2^Pu * Real.exp (π/2) / cl)| + (Pu + 3) + 1) * ℓ) :=
        mul_le_mul_of_nonneg_left hfinal (by norm_num)
    _ = 32 * (|Real.log (Cu * 2^Pu * Real.exp (π/2) / cl)| + (Pu + 3) + 1) * ℓ := by
        ring

end

end DedekindResidue
