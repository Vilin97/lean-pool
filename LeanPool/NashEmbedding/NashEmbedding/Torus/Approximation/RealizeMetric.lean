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
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Torus.Approximation.SmoothMetricApprox
import LeanPool.NashEmbedding.NashEmbedding.Torus.Approximation.BumpConstruction

/-!
# Realization of `f·B` and Theorem A

The second half of the approximation theorem: a smooth periodic nonnegative
function times a fixed bump Gram matrix `B` is a realizable metric, and every
positive-definite smooth metric is an `H^s`-limit of realizable ones.

## Main statements

* `realize_fB` — for smooth periodic `f ≥ 0` and the bump Gram matrix `B`, the
  metric `f · B` is realizable;
* `realizable_approx` — Theorem A for a fixed Sobolev index `s`;
* `realizable_approx_all_s` — Theorem A for every `s` (the form used by `nashTorus`).
-/

open scoped BigOperators ContDiff
open MeasureTheory Real Matrix
open NashEmbedding.Sobolev (periodicExtension rescale meshPoint positionSpaceRiemann
  integrationEmbed MemSobolevDistrib sobolevNormSqDistrib IsPeriodic2Pi)

noncomputable
section

namespace NashEmbedding

variable {n : ℕ}

/-! ## Leaves (Aristotle candidates) -/

/-- Local finiteness of the periodization sum: near every point only finitely many
translates of a compactly supported `φ` are nonzero, uniformly on a neighbourhood. -/
lemma exists_finset_periodicExtension {φ : (Fin n → ℝ) → ℂ} (hsupp : HasCompactSupport φ)
    (x : Fin n → ℝ) :
    ∃ (U : Set (Fin n → ℝ)) (S : Finset (Fin n → ℤ)), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ k ∉ S, φ (y + NashEmbedding.Sobolev.periodicShift n k) = 0 := by
  have h_compact_support : ∃ R : ℝ, ∀ x : Fin n → ℝ, ‖x‖ ≥ R → φ x = 0 := by
    obtain ⟨ R, hR ⟩ := hsupp.exists_pos_le_norm;
    exact ⟨ R, hR.2 ⟩;
  obtain ⟨R, hR⟩ := h_compact_support
  have h_bound : ∀ k : Fin n → ℤ, (∃ y ∈ Metric.ball x 1, φ (y +
      NashEmbedding.Sobolev.periodicShift n k) ≠ 0) →
      ∀ i : Fin n, |(k i : ℝ)| ≤ (R + ‖x‖ + 1) / (2 * Real.pi) := by
    intros k hk i
    obtain ⟨y, hy_ball, hy_nonzero⟩ := hk
    have h_bound : ‖y + NashEmbedding.Sobolev.periodicShift n k‖ < R := by
      exact lt_of_not_ge fun h => hy_nonzero <| hR _ h;
    have h_bound : |(y i + 2 * Real.pi * (k i : ℝ))| ≤ R := by
      exact le_trans ( by
        simpa [NashEmbedding.Sobolev.periodicShift] using norm_le_pi_norm ( y +
          NashEmbedding.Sobolev.periodicShift n k ) i ) h_bound.le;
    have h_bound : |y i| ≤ ‖x‖ + 1 := by
      have h_bound : |y i - x i| ≤ ‖y - x‖ := by
        exact norm_le_pi_norm ( y - x ) i;
      exact abs_le.mpr ⟨ by
        linarith [ abs_le.mp h_bound, abs_le.mp ( norm_le_pi_norm x i ), abs_le.mp (
          norm_le_pi_norm ( y - x ) i ), show ‖y - x‖ < 1 from by
          rw [← dist_eq_norm]; exact hy_ball ], by
        linarith [ abs_le.mp h_bound, abs_le.mp ( norm_le_pi_norm x i ), abs_le.mp (
          norm_le_pi_norm ( y - x ) i ), show ‖y - x‖ < 1 from by
          rw [← dist_eq_norm]; exact hy_ball ] ⟩;
    rw [ le_div_iff₀ ] <;> cases abs_cases ( k i : ℝ ) <;> cases abs_cases ( y i + 2 * Real.pi *
        ( k i : ℝ ) ) <;> cases abs_cases ( y i ) <;> nlinarith [ Real.pi_gt_three ];
  have h_finite_k : Set.Finite {k : Fin n → ℤ | ∀ i : Fin n, |(k i : ℝ)| ≤ (R + ‖x‖ + 1) / (2 *
      Real.pi)} := by
    have h_finite_k : ∀ i : Fin n, Set.Finite {k : ℤ | |(k : ℝ)| ≤ (R + ‖x‖ + 1) / (2 *
        Real.pi)} := by
      exact fun i => Set.Finite.subset ( Set.finite_Icc ( -⌈ ( R + ‖x‖ + 1 ) / ( 2 * Real.pi ) ⌉
        ) ⌈ ( R + ‖x‖ + 1 ) / ( 2 * Real.pi ) ⌉ ) fun k hk => ⟨ neg_le_of_abs_le <| by
        exact_mod_cast hk.out.trans <| Int.le_ceil _, le_of_abs_le <| by
        exact_mod_cast hk.out.trans <| Int.le_ceil _ ⟩;
    exact Set.Finite.subset ( Set.Finite.pi fun i => h_finite_k i ) fun k hk => by simpa using hk;
  have hfin : Set.Finite {k : Fin n → ℤ | ∃ y ∈ Metric.ball x 1, φ (y +
      NashEmbedding.Sobolev.periodicShift n k) ≠ 0} :=
    h_finite_k.subset fun k hk => h_bound k hk
  refine ⟨Metric.ball x 1, hfin.toFinset, Metric.isOpen_ball, Metric.mem_ball_self zero_lt_one, ?_⟩
  intro y hy k hk
  by_contra h
  exact hk (hfin.mem_toFinset.mpr ⟨y, hy, h⟩)

/-- `∂ⱼ(φ^per) = (∂ⱼφ)^per` for `φ ∈ C_c^∞(ℝⁿ; ℂ)`. -/
lemma partialDeriv_periodicExtension {φ : (Fin n → ℝ) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) (j : Fin n) :
    NashEmbedding.Sobolev.partialDeriv j (periodicExtension n φ)
      = periodicExtension n (NashEmbedding.Sobolev.partialDeriv j φ) := by
  funext x
  obtain ⟨U, S, hU, hxU, hS⟩ := exists_finset_periodicExtension hsupp x
  have hdiff : Differentiable ℝ φ := hφ.differentiable NashEmbedding.Sobolev.infty_ne_zero
  -- near x, the periodization is a finite sum
  have hev : periodicExtension n φ =ᶠ[nhds x]
      fun y => ∑ k ∈ S, φ (y + NashEmbedding.Sobolev.periodicShift n k) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    unfold periodicExtension
    exact tsum_eq_sum (fun k hk => hS y hy k hk)
  unfold NashEmbedding.Sobolev.partialDeriv
  rw [hev.fderiv_eq]
  have hsum0 : HasFDerivAt (∑ k ∈ S, fun y => φ (y + NashEmbedding.Sobolev.periodicShift n k))
      (∑ k ∈ S, fderiv ℝ φ (x + NashEmbedding.Sobolev.periodicShift n k)) x := by
    refine HasFDerivAt.sum fun k _ => ?_
    exact (hdiff (x + NashEmbedding.Sobolev.periodicShift n k)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const (NashEmbedding.Sobolev.periodicShift n k))
  have hsum : HasFDerivAt (fun y => ∑ k ∈ S, φ (y + NashEmbedding.Sobolev.periodicShift n k))
      (∑ k ∈ S, fderiv ℝ φ (x + NashEmbedding.Sobolev.periodicShift n k)) x := by
    convert hsum0 using 1
    funext y; simp [Finset.sum_apply]
  rw [hsum.fderiv, _root_.sum_apply]
  -- the right-hand side is the same finite sum: the other terms vanish
  unfold periodicExtension
  rw [tsum_eq_sum (s := S)]
  intro k hk
  change fderiv ℝ φ (x + NashEmbedding.Sobolev.periodicShift n k) (Pi.single j 1) = 0
  -- φ ∘ (· + shift k) vanishes on the open set U ∋ x, so its derivative vanishes at x
  have hz : (fun y => φ (y + NashEmbedding.Sobolev.periodicShift n k)) =ᶠ[nhds x] fun _ => (0 :
      ℂ) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact hS y hy k hk
  rw [← fderiv_comp_add_right, hz.fderiv_eq]
  simp
/-- At most one translate `x + 2πk` lies in `(-π,π)ⁿ`. -/
lemma periodicShift_unique {x : Fin n → ℝ} {k k' : Fin n → ℤ}
    (hk : ∀ j : Fin n, |(x + NashEmbedding.Sobolev.periodicShift n k) j| < π)
    (hk' : ∀ j : Fin n, |(x + NashEmbedding.Sobolev.periodicShift n k') j| < π) : k = k' := by
  funext j
  have h1 := hk j
  have h2 := hk' j
  simp only [Pi.add_apply, NashEmbedding.Sobolev.periodicShift] at h1 h2
  have h3 : |(2 * π) * ((k j : ℝ) - (k' j : ℝ))| < 2 * π := by
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
    rw [abs_lt]; constructor <;> linarith
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)] at h3
  have h4 : |((k j - k' j : ℤ) : ℝ)| < 1 := by
    push_cast; nlinarith [Real.pi_pos]
  have h5 : |k j - k' j| < 1 := by exact_mod_cast h4
  have h6 : k j - k' j = 0 := Int.abs_lt_one_iff.mp h5
  linarith

/-- Products of periodic extensions of functions supported in `(-π,π)ⁿ`. -/
lemma periodicExtension_mul {φ ψ : (Fin n → ℝ) → ℂ}
    (hφ : ∀ x, φ x ≠ 0 → ∀ j : Fin n, |x j| < π)
    (hψ : ∀ x, ψ x ≠ 0 → ∀ j : Fin n, |x j| < π) (x : Fin n → ℝ) :
    periodicExtension n φ x * periodicExtension n ψ x
      = periodicExtension n (fun y => φ y * ψ y) x := by
  unfold periodicExtension
  by_cases hex : ∃ k₀ : Fin n → ℤ, ∀ j : Fin n, |(x + NashEmbedding.Sobolev.periodicShift n k₀)
      j| < π
  · obtain ⟨k₀, hk₀⟩ := hex
    have hφ0 : ∀ k ≠ k₀, φ (x + NashEmbedding.Sobolev.periodicShift n k) = 0 := by
      intro k hk; by_contra h
      exact hk (periodicShift_unique (hφ _ h) hk₀)
    have hψ0 : ∀ k ≠ k₀, ψ (x + NashEmbedding.Sobolev.periodicShift n k) = 0 := by
      intro k hk; by_contra h
      exact hk (periodicShift_unique (hψ _ h) hk₀)
    rw [tsum_eq_single k₀ hφ0, tsum_eq_single k₀ hψ0,
      tsum_eq_single k₀ (fun k hk => by
        change φ (x + NashEmbedding.Sobolev.periodicShift n k) * ψ (x +
            NashEmbedding.Sobolev.periodicShift n k) = 0
        rw [hφ0 k hk, zero_mul])]
  · push Not at hex
    have hφ0 : ∀ k, φ (x + NashEmbedding.Sobolev.periodicShift n k) = 0 := by
      intro k; by_contra h
      obtain ⟨j, hj⟩ := hex k
      exact absurd (hφ _ h j) (not_lt.mpr hj)
    simp [hφ0]

/-- The `ε`-rescaling `χ_ε(x) = ε^{1-n/2} χ(x/ε)` of a real bump. -/
def rescaleBump (n : ℕ) (χ : (Fin n → ℝ) → ℝ) (ε : ℝ) (x : Fin n → ℝ) : ℝ :=
  ε ^ (1 - (n : ℝ) / 2) * χ (ε⁻¹ • x)

/-- `∂ᵢχ_ε ∂ⱼχ_ε = ε^{-n} (∂ᵢχ ∂ⱼχ)(·/ε)`, i.e. the `rescale` of `∂ᵢχ ∂ⱼχ`. -/
lemma rescaleBump_fderiv_mul {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) {ε : ℝ} (hε : 0 < ε)
    (i j : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (rescaleBump n χ ε) x (Pi.single i 1) * fderiv ℝ (rescaleBump n χ ε) x (Pi.single j 1)
      = (ε⁻¹) ^ n * (fderiv ℝ χ (ε⁻¹ • x) (Pi.single i 1) * fderiv ℝ χ (ε⁻¹ • x) (Pi.single j
          1)) := by
  set c : ℝ := ε ^ (1 - (n : ℝ) / 2) with hc
  have hd : ∀ v : Fin n → ℝ, fderiv ℝ (rescaleBump n χ ε) x v
      = c * (ε⁻¹ * fderiv ℝ χ (ε⁻¹ • x) v) := by
    intro v
    have hin : HasFDerivAt (fun y : Fin n → ℝ => χ (ε⁻¹ • y))
        ((fderiv ℝ χ (ε⁻¹ • x)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ (Fin n → ℝ))) x := by
      exact (hχ.differentiable NashEmbedding.Sobolev.infty_ne_zero (ε⁻¹ • x)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul ε⁻¹)
    have hall : HasFDerivAt (rescaleBump n χ ε)
        (c • ((fderiv ℝ χ (ε⁻¹ • x)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ (Fin n → ℝ)))) x :=
      hin.const_mul c
    rw [hall.fderiv]
    simp [smul_eq_mul]
  rw [hd, hd]
  have hcε : c * ε⁻¹ = ε ^ (-(n : ℝ) / 2) := by
    rw [hc, ← Real.rpow_neg_one ε, ← Real.rpow_add hε]
    congr 1; ring
  have hsq : (ε ^ (-(n : ℝ) / 2)) ^ 2 = (ε⁻¹) ^ n := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hε.le, inv_pow, ← Real.rpow_natCast,
      ← Real.rpow_neg hε.le]
    congr 1; push_cast; ring
  calc c * (ε⁻¹ * fderiv ℝ χ (ε⁻¹ • x) (Pi.single i 1)) *
        (c * (ε⁻¹ * fderiv ℝ χ (ε⁻¹ • x) (Pi.single j 1)))
      = (c * ε⁻¹) ^ 2 * (fderiv ℝ χ (ε⁻¹ • x) (Pi.single i 1) * fderiv ℝ χ (ε⁻¹ • x) (Pi.single
          j 1)) := by
        ring
    _ = (ε⁻¹) ^ n * (fderiv ℝ χ (ε⁻¹ • x) (Pi.single i 1) * fderiv ℝ χ (ε⁻¹ • x) (Pi.single j
        1)) := by
        rw [hcε, hsq]

/-! ## Gram of a concatenation; the translated periodized bump -/

/-- The Gram entries of a vector-valued map are sums over components. -/
lemma gram_dot_eq_sum {ι : Type*} [Fintype ι] {u : ι → (Fin n → ℝ) → ℝ}
    (hu : ∀ k, Differentiable ℝ (u k)) (v w : Fin n → ℝ) (x : Fin n → ℝ) :
    dotProduct (fderiv ℝ (fun x k => u k x) x v) (fderiv ℝ (fun x k => u k x) x w)
      = ∑ k, fderiv ℝ (u k) x v * fderiv ℝ (u k) x w := by
  unfold dotProduct
  have hf : HasFDerivAt (fun x k => u k x) (ContinuousLinearMap.pi fun k => fderiv ℝ (u k) x) x :=
    hasFDerivAt_pi.mpr fun k => (hu k x).hasFDerivAt
  rw [hf.fderiv]
  simp [ContinuousLinearMap.pi_apply]

/-- Complexification of a real function. -/
def cplx (χ : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℂ := fun x => (χ x : ℂ)

lemma cplx_contDiff {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (cplx χ) :=
  Complex.ofRealCLM.contDiff.comp hχ

lemma cplx_hasCompactSupport {χ : (Fin n → ℝ) → ℝ} (h : HasCompactSupport χ) :
    HasCompactSupport (cplx χ) :=
  h.comp_left (g := Complex.ofReal) Complex.ofReal_zero

lemma cplx_im (χ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : (cplx χ x).im = 0 := by simp [cplx]

lemma cplx_ne_zero_iff (χ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : cplx χ x ≠ 0 ↔ χ x ≠ 0 := by
  simp [cplx]

lemma partialDeriv_cplx {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (j : Fin n) :
    NashEmbedding.Sobolev.partialDeriv j (cplx χ) = cplx (fun x => fderiv ℝ χ x (Pi.single j 1))
        := by
  funext x
  unfold NashEmbedding.Sobolev.partialDeriv
  have h := (Complex.ofRealCLM.hasFDerivAt (x := χ x)).comp x
    ((hχ.differentiable NashEmbedding.Sobolev.infty_ne_zero) x).hasFDerivAt
  have heq : cplx χ = ⇑Complex.ofRealCLM ∘ χ := rfl
  rw [heq, h.fderiv]
  simp [cplx]

/-- Derivatives of a function supported in the `π/2`-box are supported in the open `π`-cube. -/
lemma fderiv_cube_of_half {χ : (Fin n → ℝ) → ℝ}
    (hcube : ∀ x, χ x ≠ 0 → ∀ j : Fin n, |x j| < π / 2) (v : Fin n → ℝ) :
    ∀ x, fderiv ℝ χ x v ≠ 0 → ∀ j : Fin n, |x j| < π := by
  intro x hx j
  have hmem : x ∈ tsupport χ := by
    apply support_fderiv_subset (𝕜 := ℝ)
    intro h0
    apply hx
    rw [h0]; simp
  have hclosed : IsClosed {y : Fin n → ℝ | ∀ j, |y j| ≤ π / 2} := by
    have : {y : Fin n → ℝ | ∀ j, |y j| ≤ π / 2} = ⋂ j, {y | |y j| ≤ π / 2} := by
      ext y; simp
    rw [this]
    exact isClosed_iInter fun j => isClosed_le (continuous_apply j).abs continuous_const
  have hsub : tsupport χ ⊆ {y : Fin n → ℝ | ∀ j, |y j| ≤ π / 2} :=
    closure_minimal (fun y hy j => (hcube y hy j).le) hclosed
  have := hsub hmem j
  linarith [Real.pi_pos]

/-- Real periodic extension of a real bump. -/
def pe (n : ℕ) (χ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (periodicExtension n (cplx χ) x).re

lemma pe_contDiff {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ) :
    ContDiff ℝ ∞ (pe n χ) :=
  Complex.reCLM.contDiff.comp
    (NashEmbedding.Sobolev.periodicExtension_contDiff (cplx_contDiff hχ) (cplx_hasCompactSupport
        hs))

/-- `∂ⱼ (pe χ) = pe (∂ⱼ χ)`. -/
lemma fderiv_pe {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ)
    (j : Fin n) (y : Fin n → ℝ) :
    fderiv ℝ (pe n χ) y (Pi.single j 1) = pe n (fun x => fderiv ℝ χ x (Pi.single j 1)) y := by
  have hF : Differentiable ℝ (periodicExtension n (cplx χ)) :=
    (NashEmbedding.Sobolev.periodicExtension_contDiff (cplx_contDiff hχ) (cplx_hasCompactSupport
        hs))
      |>.differentiable NashEmbedding.Sobolev.infty_ne_zero
  have h := (Complex.reCLM.hasFDerivAt (x := periodicExtension n (cplx χ) y)).comp y
    (hF y).hasFDerivAt
  have heq : pe n χ = ⇑Complex.reCLM ∘ periodicExtension n (cplx χ) := rfl
  rw [heq, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  have h1 := congrFun (partialDeriv_periodicExtension (cplx_contDiff hχ) (cplx_hasCompactSupport
      hs) j) y
  unfold NashEmbedding.Sobolev.partialDeriv at h1
  have h2 := partialDeriv_cplx hχ j
  unfold NashEmbedding.Sobolev.partialDeriv at h2
  rw [h1, h2]
  rfl

/-- Gram entries of the translated, scaled, periodized bump. -/
lemma gram_pe_bump {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ)
    (hcube : ∀ x, χ x ≠ 0 → ∀ j : Fin n, |x j| < π / 2) (a : ℝ) (z : Fin n → ℝ)
    (i j : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (fun x => a * pe n χ (x - z)) x (Pi.single i 1)
      * fderiv ℝ (fun x => a * pe n χ (x - z)) x (Pi.single j 1)
      = a ^ 2 * pe n (fun y => fderiv ℝ χ y (Pi.single i 1) * fderiv ℝ χ y (Pi.single j 1)) (x -
          z) := by
  have hpe : Differentiable ℝ (pe n χ) := (pe_contDiff hχ hs).differentiable
      NashEmbedding.Sobolev.infty_ne_zero
  -- derivative of the translate
  have hd : ∀ v : Fin n → ℝ, fderiv ℝ (fun x => a * pe n χ (x - z)) x v
      = a * fderiv ℝ (pe n χ) (x - z) v := by
    intro v
    have h1 : HasFDerivAt (fun x => pe n χ (x - z)) (fderiv ℝ (pe n χ) (x - z)) x := by
      exact (hpe (x - z)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)
    rw [(h1.const_mul a).fderiv]
    simp
  rw [hd, hd, fderiv_pe hχ hs, fderiv_pe hχ hs]
  -- product of real parts = real part of product, and periodization of product
  unfold pe
  have him : ∀ ψ : (Fin n → ℝ) → ℝ, HasCompactSupport ψ → ∀ y,
      (periodicExtension n (cplx ψ) y).im = 0 := fun ψ hψ y =>
    NashEmbedding.Sobolev.periodicExtension_im_zero (cplx_im ψ) y
  have hsi : HasCompactSupport (fun y => fderiv ℝ χ y (Pi.single i 1)) := hs.fderiv_apply ℝ _
  have hsj : HasCompactSupport (fun y => fderiv ℝ χ y (Pi.single j 1)) := hs.fderiv_apply ℝ _
  have hmul := periodicExtension_mul (n := n)
    (φ := cplx (fun y => fderiv ℝ χ y (Pi.single i 1)))
    (ψ := cplx (fun y => fderiv ℝ χ y (Pi.single j 1)))
    (fun y hy => fderiv_cube_of_half hcube _ y
      ((cplx_ne_zero_iff (fun y => fderiv ℝ χ y (Pi.single i 1)) y).mp hy))
    (fun y hy => fderiv_cube_of_half hcube _ y
      ((cplx_ne_zero_iff (fun y => fderiv ℝ χ y (Pi.single j 1)) y).mp hy)) (x - z)
  have hre : (periodicExtension n (cplx fun y => fderiv ℝ χ y (Pi.single i 1)) (x - z)).re
      * (periodicExtension n (cplx fun y => fderiv ℝ χ y (Pi.single j 1)) (x - z)).re
      = (periodicExtension n (cplx fun y => fderiv ℝ χ y (Pi.single i 1)) (x - z)
        * periodicExtension n (cplx fun y => fderiv ℝ χ y (Pi.single j 1)) (x - z)).re := by
    rw [Complex.mul_re, him _ hsi, him _ hsj]; ring
  have hc : (fun y => cplx (fun y => fderiv ℝ χ y (Pi.single i 1)) y
      * cplx (fun y => fderiv ℝ χ y (Pi.single j 1)) y)
      = cplx (fun y => fderiv ℝ χ y (Pi.single i 1) * fderiv ℝ χ y (Pi.single j 1)) := by
    funext y; simp [cplx]
  calc a * (periodicExtension n (cplx fun y => fderiv ℝ χ y (Pi.single i 1)) (x - z)).re
        * (a * (periodicExtension n (cplx fun y => fderiv ℝ χ y (Pi.single j 1)) (x - z)).re)
      = a ^ 2 * ((periodicExtension n (cplx fun y => fderiv ℝ χ y (Pi.single i 1)) (x - z)).re
          * (periodicExtension n (cplx fun y => fderiv ℝ χ y (Pi.single j 1)) (x - z)).re) := by
            ring
    _ = _ := by rw [hre, hmul, hc]

/-! ## The concatenated bump family and its Gram matrix -/

/-- The family `u_k(x) = √(δⁿ f(z_k)) · pe χ (x − z_k)` over mesh points `z_k = meshPoint n M k`,
packaged as a map `ℝⁿ → ℝ^{(Fin n → Fin M)}`. -/
def bumpFamily (n : ℕ) (χ : (Fin n → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ) (M : ℕ)
    (x : Fin n → ℝ) : (Fin n → Fin M) → ℝ :=
  fun k => Real.sqrt ((2 * π / (M : ℝ)) ^ n * f (meshPoint n M k)) * pe n χ (x - meshPoint n M k)

/-- Gram entries of the bump family: the position-space Riemann sum of `f` against
`(∂ᵢχ ∂ⱼχ)^per`. -/
lemma gram_bumpFamily {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ)
    (hcube : ∀ x, χ x ≠ 0 → ∀ j : Fin n, |x j| < π / 2)
    {f : (Fin n → ℝ) → ℝ} (hf0 : ∀ x, 0 ≤ f x) {M : ℕ} (hM : 0 < M) (i j : Fin n)
    (x : Fin n → ℝ) :
    dotProduct (fderiv ℝ (bumpFamily n χ f M) x (Pi.single i 1))
        (fderiv ℝ (bumpFamily n χ f M) x (Pi.single j 1))
      = (2 * π / (M : ℝ)) ^ n * ∑ k : Fin n → Fin M,
          pe n (fun y => fderiv ℝ χ y (Pi.single i 1) * fderiv ℝ χ y (Pi.single j 1))
            (x - meshPoint n M k) * f (meshPoint n M k) := by
  have hpe : Differentiable ℝ (pe n χ) := (pe_contDiff hχ hs).differentiable
      NashEmbedding.Sobolev.infty_ne_zero
  have hu : ∀ k : Fin n → Fin M, Differentiable ℝ
      (fun x => Real.sqrt ((2 * π / (M : ℝ)) ^ n * f (meshPoint n M k))
        * pe n χ (x - meshPoint n M k)) :=
    fun k => (differentiable_const _).mul (hpe.comp (differentiable_id.sub_const _))
  have h := gram_dot_eq_sum (n := n) (ι := Fin n → Fin M)
    (u := fun k x => Real.sqrt ((2 * π / (M : ℝ)) ^ n * f (meshPoint n M k))
      * pe n χ (x - meshPoint n M k)) hu (Pi.single i 1) (Pi.single j 1) x
  unfold bumpFamily
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gram_pe_bump hχ hs hcube _ (meshPoint n M k) i j x,
    Real.sq_sqrt (mul_nonneg (by positivity) (hf0 _))]
  ring

/-! ## Per-entry residual bound with a scalar target -/

open NashEmbedding.Sobolev (riemannSumDistrib convDistrib fourierSynthesis fourierCoeffDistrib
  fourierCoeffDistrib_integrationEmbed stdFourierCoeff seqToDual)

lemma integrationEmbed_const_mul (c : ℝ) (g : (Fin n → ℝ) → ℝ) :
    integrationEmbed n (fun x => ((c * g x : ℝ) : ℂ))
      = (c : ℂ) • integrationEmbed n (fun y => ((g y : ℝ) : ℂ)) := by
  unfold NashEmbedding.Sobolev.integrationEmbed
  rw [← NashEmbedding.Sobolev.seqToDual_smul]
  congr 1
  funext m
  unfold NashEmbedding.Sobolev.stdFourierCoeff
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

lemma memSobolevDistrib_smul {s : ℝ} {u : NashEmbedding.Sobolev.TrigPolyDual n}
    (hu : MemSobolevDistrib n s u)
    (c : ℂ) : MemSobolevDistrib n s (c • u) := by
  unfold NashEmbedding.Sobolev.MemSobolevDistrib NashEmbedding.Sobolev.MemSobolev at *
  have h : ∀ m, NashEmbedding.Sobolev.weight n s m * ‖fourierCoeffDistrib (c • u) m‖ ^ 2
      = ‖c‖ ^ 2 * (NashEmbedding.Sobolev.weight n s m * ‖fourierCoeffDistrib u m‖ ^ 2) := by
    intro m
    rw [NashEmbedding.Sobolev.fourierCoeffDistrib_smul_complex, norm_mul, mul_pow]
    ring
  simp_rw [h]
  exact hu.mul_left _

/-- Per-entry quasi-triangle bound against a scalar multiple `c · g` of the target
(generalizes the Step-1 assembly lemma, where `c = 1`). -/
lemma perEntry_residual_bound_c
    (hn : 0 < n) {s : ℝ} (hs : (n : ℝ) < 2 * s)
    {φ : (Fin n → ℝ) → ℂ}
    (hφ_sm : ContDiff ℝ ∞ φ) (hφ_supp : HasCompactSupport φ)
    (hφ_cube : ∀ x, φ x ≠ 0 → ∀ j : Fin n, |x j| < Real.pi)
    (hφ_im : ∀ x, (φ x).im = 0)
    {g : (Fin n → ℝ) → ℝ} (hg_sm : ContDiff ℝ ∞ g) (hg_per : IsPeriodic2Pi g)
    {M : ℕ} (c : ℝ) :
    sobolevNormSqDistrib n s
      (integrationEmbed n (fun x : (Fin n → ℝ) =>
        (((2 * Real.pi / (M : ℝ)) ^ n
            * ∑ k : Fin n → Fin M,
                (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
                * g (meshPoint n M k) - c * g x : ℝ) : ℂ)))
      ≤ 2 * sobolevNormSqDistrib n s
          (riemannSumDistrib n φ (integrationEmbed n (fun y => (g y : ℂ))) M
            - convDistrib n φ (integrationEmbed n (fun y => (g y : ℂ))))
      + 2 * sobolevNormSqDistrib n s
          (convDistrib n φ (integrationEmbed n (fun y => (g y : ℂ)))
            - (c : ℂ) • integrationEmbed n (fun y => (g y : ℂ))) := by
  have hgC_sm : ContDiff ℝ ∞ (fun y : (Fin n → ℝ) => (g y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hg_sm
  have hgC_per : IsPeriodic2Pi (fun y : (Fin n → ℝ) => (g y : ℂ)) := by
    intro x k
    change ((g (x + NashEmbedding.Sobolev.periodicShift n k) : ℝ) : ℂ) = ((g x : ℝ) : ℂ)
    rw [hg_per x k]
  have hgC_memSob : MemSobolevDistrib n s (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) :=
    NashEmbedding.Sobolev.smooth_periodic_memSobolevDistrib hn hgC_sm hgC_per s
  have hφ_int : Integrable φ :=
    hφ_sm.continuous.integrable_of_hasCompactSupport hφ_supp
  have hφ_rd : NashEmbedding.Sobolev.FTRapidDecay n φ := NashEmbedding.Sobolev.cinfty_rapidDecay
      hn hφ_sm hφ_supp
  have h_pe_im : ∀ y, (periodicExtension n φ y).im = 0 :=
    NashEmbedding.Sobolev.periodicExtension_im_zero hφ_im
  have h_fs_mesh : ∀ k : Fin n → Fin M,
      fourierSynthesis n
        (fourierCoeffDistrib (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))))
        (meshPoint n M k)
      = ((g (meshPoint n M k) : ℝ) : ℂ) := by
    intro k
    rw [fourierCoeffDistrib_integrationEmbed]
    exact NashEmbedding.Sobolev.fourierSynthesis_stdFourierCoeff_of_smoothPeriodic hn hgC_sm
        hgC_per _
  have h_psr_pt : ∀ x : (Fin n → ℝ),
      positionSpaceRiemann n φ
        (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) M x
        = (((2 * Real.pi / (M : ℝ)) ^ n
            * ∑ k : Fin n → Fin M,
                (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
                * g (meshPoint n M k) : ℝ) : ℂ) := by
    intro x
    unfold NashEmbedding.Sobolev.positionSpaceRiemann
    simp only [h_fs_mesh]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have h_eq : periodicExtension n φ (fun j => x j - meshPoint n M k j)
        = ((periodicExtension n φ (fun j => x j - meshPoint n M k j)).re : ℂ) := by
      apply Complex.ext
      · simp
      · rw [Complex.ofReal_im]; exact h_pe_im _
    rw [h_eq]
    simp only [Complex.ofReal_re]
  have h_iE_eq :
      integrationEmbed n
        (positionSpaceRiemann n φ
          (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) M)
      = integrationEmbed n (fun x : (Fin n → ℝ) =>
          (((2 * Real.pi / (M : ℝ)) ^ n
            * ∑ k : Fin n → Fin M,
                (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
                * g (meshPoint n M k) : ℝ) : ℂ)) := by
    congr 1
    funext x
    exact h_psr_pt x
  have hBridge := NashEmbedding.Sobolev.riemann_positionSpace hφ_sm hφ_supp hφ_cube
    (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) M
  have h_R_eq :
      riemannSumDistrib n φ (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) M
        = integrationEmbed n (fun x : (Fin n → ℝ) =>
            (((2 * Real.pi / (M : ℝ)) ^ n
              * ∑ k : Fin n → Fin M,
                  (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
                  * g (meshPoint n M k) : ℝ) : ℂ)) := by
    rw [hBridge, h_iE_eq]
  have h_LHS_split : (fun x : (Fin n → ℝ) =>
        (((2 * Real.pi / (M : ℝ)) ^ n
            * ∑ k : Fin n → Fin M,
                (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
                * g (meshPoint n M k) - c * g x : ℝ) : ℂ))
      = (fun x : (Fin n → ℝ) =>
          (((2 * Real.pi / (M : ℝ)) ^ n
            * ∑ k : Fin n → Fin M,
                (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
                * g (meshPoint n M k) : ℝ) : ℂ) - ((c * g x : ℝ) : ℂ)) := by
    funext x; push_cast; ring
  have h_pe_contDiff : ContDiff ℝ ∞ (periodicExtension n φ) :=
    NashEmbedding.Sobolev.periodicExtension_contDiff hφ_sm hφ_supp
  have h_convex_combo_cts : Continuous (fun x : (Fin n → ℝ) =>
      (((2 * Real.pi / (M : ℝ)) ^ n
          * ∑ k : Fin n → Fin M,
              (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
              * g (meshPoint n M k) : ℝ) : ℂ)) := by
    refine Complex.ofRealCLM.continuous.comp ?_
    refine continuous_const.mul ?_
    apply continuous_finsetSum
    intro k _
    refine Continuous.mul ?_ continuous_const
    refine Complex.reCLM.continuous.comp ?_
    refine h_pe_contDiff.continuous.comp ?_
    exact continuous_pi (fun j => (continuous_apply j).sub continuous_const)
  have h_gC_cts : Continuous (fun x : (Fin n → ℝ) => ((c * g x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.comp (continuous_const.mul hg_sm.continuous)
  rw [h_LHS_split, NashEmbedding.Sobolev.integrationEmbed_sub h_convex_combo_cts h_gC_cts, ← h_R_eq,
    integrationEmbed_const_mul]
  have hR_memSob :
      MemSobolevDistrib n s
        (riemannSumDistrib n φ (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) M) :=
    NashEmbedding.Sobolev.riemannSumDistrib_memSobolevDistrib hφ_rd hn hs hgC_memSob M
  have hB_memSob :
      MemSobolevDistrib n s
        (convDistrib n φ (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ)))) :=
    NashEmbedding.Sobolev.convDistrib_memSobolevDistrib hφ_int hgC_memSob
  exact NashEmbedding.Sobolev.sobolevNormSqDistrib_triangle s _ _ _
    (hR_memSob.sub hB_memSob) (hB_memSob.sub (memSobolevDistrib_smul hgC_memSob _))

/-! ## Small helpers for the assembly -/

lemma sobolevNormSqDistrib_smul (s : ℝ) (c : ℂ) (u : NashEmbedding.Sobolev.TrigPolyDual n) :
    sobolevNormSqDistrib n s (c • u) = ‖c‖ ^ 2 * sobolevNormSqDistrib n s u := by
  unfold NashEmbedding.Sobolev.sobolevNormSqDistrib NashEmbedding.Sobolev.sobolevNormSq
  rw [← tsum_mul_left]
  congr 1; funext m
  rw [NashEmbedding.Sobolev.fourierCoeffDistrib_smul_complex, norm_mul, mul_pow]
  ring

/-- Reindexing the codomain of a vector-valued map by an equivalence preserves Gram entries. -/
lemma gram_dot_reindex {ι : Type*} [Fintype ι] {N : ℕ} (e : ι ≃ Fin N)
    {U : (Fin n → ℝ) → (ι → ℝ)} (hU : Differentiable ℝ U) (v w : Fin n → ℝ) (x : Fin n → ℝ) :
    dotProduct (fderiv ℝ (fun x m => U x (e.symm m)) x v) (fderiv ℝ (fun x m => U x (e.symm m)) x w)
      = dotProduct (fderiv ℝ U x v) (fderiv ℝ U x w) := by
  have hcomp : ∀ k : ι, HasFDerivAt (fun x => U x k)
      ((ContinuousLinearMap.proj k).comp (fderiv ℝ U x)) x :=
    hasFDerivAt_pi'.mp (hU x).hasFDerivAt
  have hf : HasFDerivAt (fun x m => U x (e.symm m))
      (ContinuousLinearMap.pi fun m => (ContinuousLinearMap.proj (e.symm m)).comp (fderiv ℝ U
          x)) x :=
    hasFDerivAt_pi.mpr fun m => hcomp (e.symm m)
  rw [hf.fderiv]
  unfold dotProduct
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  exact Equiv.sum_comp e.symm (fun k => fderiv ℝ U x v k * fderiv ℝ U x w k)

lemma pe_isPeriodic2Pi (χ : (Fin n → ℝ) → ℝ) : IsPeriodic2Pi (pe n χ) := by
  intro x k
  unfold pe
  rw [NashEmbedding.Sobolev.periodicExtension_isPeriodic2Pi]

lemma bumpFamily_smoothPeriodic {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (f : (Fin n → ℝ) → ℝ) (M : ℕ) :
    SmoothPeriodic (bumpFamily n χ f M) := by
  constructor
  · unfold bumpFamily
    refine contDiff_pi.mpr fun k => ?_
    exact contDiff_const.mul ((pe_contDiff hχ hs).comp (contDiff_id.sub contDiff_const))
  · intro x l
    funext k
    unfold bumpFamily
    congr 1
    have : x + NashEmbedding.Sobolev.periodicShift n l - meshPoint n M k
        = (x - meshPoint n M k) + NashEmbedding.Sobolev.periodicShift n l := by abel
    rw [this, pe_isPeriodic2Pi]

/-! ## Rescaled bump: properties -/

lemma rescaleBump_contDiff {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (ε : ℝ) :
    ContDiff ℝ ∞ (rescaleBump n χ ε) :=
  contDiff_const.mul (hχ.comp (contDiff_const_smul ε⁻¹))

lemma rescaleBump_hasCompactSupport {χ : (Fin n → ℝ) → ℝ} (hs : HasCompactSupport χ)
    {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (rescaleBump n χ ε) := by
  have h : HasCompactSupport (fun x => χ (ε⁻¹ • x)) := by
    convert hs.comp_smul (inv_ne_zero hε.ne') using 1
  rw [hasCompactSupport_iff_eventuallyEq] at *
  filter_upwards [h] with x hx using by simp [rescaleBump, hx]

lemma rescaleBump_cube {χ : (Fin n → ℝ) → ℝ} (hcube : ∀ x, χ x ≠ 0 → ∀ j : Fin n, |x j| < π)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∀ x, rescaleBump n χ ε x ≠ 0 → ∀ j : Fin n, |x j| < π / 2 := by
  intro x hx j
  have h1 : χ (ε⁻¹ • x) ≠ 0 := by
    intro h0; apply hx; simp [rescaleBump, h0]
  have h2 := hcube _ h1 j
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hε] at h2
  have h3 : |x j| < ε * π := by
    rw [inv_mul_lt_iff₀ hε] at h2; exact h2
  nlinarith [Real.pi_pos]

lemma sobolevNormSqDistrib_nonneg (s : ℝ) (u : NashEmbedding.Sobolev.TrigPolyDual n) :
    0 ≤ sobolevNormSqDistrib n s u := by
  unfold NashEmbedding.Sobolev.sobolevNormSqDistrib NashEmbedding.Sobolev.sobolevNormSq
  exact tsum_nonneg fun m => mul_nonneg (NashEmbedding.Sobolev.weight_nonneg _ _) (sq_nonneg _)

/-- `ftRn` of the complexification of a real integrable function at `0`. -/
lemma ftRn_cplx_zero {F : (Fin n → ℝ) → ℝ} :
    NashEmbedding.Sobolev.ftRn n (cplx F) 0 = ((∫ y, F y : ℝ) : ℂ) := by
  rw [NashEmbedding.Sobolev.ftRn_at_zero]
  exact integral_complex_ofReal

/-! ## Realization of `f · B` -/

/-- Entrywise Sobolev discrepancy between the Gram of `U` and a target matrix function. -/
def gramDefect (n : ℕ) {N : ℕ} (U : (Fin n → ℝ) → (Fin N → ℝ))
    (G : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
        NashEmbedding.Sobolev.TrigPolyDual n :=
  integrationEmbed n (fun x =>
    ((dotProduct (partialDeriv i U x) (partialDeriv j U x) - G x i j : ℝ) : ℂ))

/-- One scale controls the mollifier errors for all entries of a bump's Gram matrix. -/
private theorem bump_mollifier_uniform_error {s ηSq : ℝ}
    {χ : (Fin n → ℝ) → ℝ} {F : Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {fC : (Fin n → ℝ) → ℂ}
    (hF_int : ∀ i j, Integrable (cplx (F i j)))
    (hF_ft0 : ∀ i j, NashEmbedding.Sobolev.ftRn n (cplx (F i j)) 0 = ((gram χ i j : ℝ) : ℂ))
    (hfC_mem : MemSobolevDistrib n s (integrationEmbed n fC)) (hηSq_pos : 0 < ηSq) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ∀ i j : Fin n,
      sobolevNormSqDistrib n s
        (convDistrib n (NashEmbedding.Sobolev.rescale n (cplx (F i j)) ε) (integrationEmbed n fC)
          - ((gram χ i j : ℝ) : ℂ) • integrationEmbed n fC) < ηSq / 4 := by
  have h_each : ∀ ij : Fin n × Fin n, ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      sobolevNormSqDistrib n s
        (convDistrib n (NashEmbedding.Sobolev.rescale n (cplx (F ij.1 ij.2)) ε)
            (integrationEmbed n fC)
          - ((gram χ ij.1 ij.2 : ℝ) : ℂ) • integrationEmbed n fC) < ηSq / 4 := by
    rintro ⟨i, j⟩
    have h := NashEmbedding.Sobolev.mollifier_convergence (cplx (F i j)) (hF_int i j) (hu :=
        hfC_mem) (s := s)
    rw [hF_ft0 i j] at h
    exact h.eventually_lt_const (by positivity)
  have h_all := Filter.eventually_all.mpr h_each
  obtain ⟨δ, hδ_pos, hδ⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp h_all
  refine ⟨min (δ / 2) (1 / 2), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by norm_num)
  · exact min_le_right _ _
  · intro i j
    exact hδ ⟨lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩ ⟨i, j⟩

/-- **Realization of `f·B`** (plan §3): for smooth periodic `f ≥ 0`, PSD `B`, `2s > n`, `η > 0`,
a smooth periodic `U` whose Gram matrix is within `η` of `f·B` in `H^s` (entrywise
sum of squared norms). -/
theorem realize_fB (hn : 0 < n) {f : (Fin n → ℝ) → ℝ} (hf : SmoothPeriodic f)
    (hf0 : ∀ x, 0 ≤ f x) {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef)
    {s : ℝ} (hs : (n : ℝ) < 2 * s) {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (U : (Fin n → ℝ) → (Fin N → ℝ)), SmoothPeriodic U ∧
      (∀ i j, MemSobolevDistrib n s (gramDefect n U (fun x => f x • B) i j)) ∧
      ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (gramDefect n U (fun x => f x • B) i j)
        < η ^ 2 := by
  classical
  -- ── complexified f ──
  set fC : (Fin n → ℝ) → ℂ := fun y => (f y : ℂ) with hfC
  have hfC_sm : ContDiff ℝ ∞ fC := Complex.ofRealCLM.contDiff.comp hf.smooth
  have hfC_per : IsPeriodic2Pi fC := by
    intro x k; simp only [hfC]; rw [hf.periodic x k]
  have hfC_mem : MemSobolevDistrib n s (integrationEmbed n fC) :=
    NashEmbedding.Sobolev.smooth_periodic_memSobolevDistrib hn hfC_sm hfC_per s
  -- ── budgets ──
  set nR : ℝ := (n : ℝ) with hnR
  have hnR_pos : 0 < nR := Nat.cast_pos.mpr hn
  set ηSq : ℝ := η ^ 2 / (3 * nR ^ 2) with hηSq
  have hηSq_pos : 0 < ηSq := by positivity
  set Nf : ℝ := sobolevNormSqDistrib n s (integrationEmbed n fC) with hNf
  have hNf_nn : 0 ≤ Nf := sobolevNormSqDistrib_nonneg s _
  set K : ℝ := Real.sqrt (ηSq / (4 * (Nf + 1))) with hK
  have hK_pos : 0 < K := Real.sqrt_pos.mpr (by positivity)
  have hK_sq : K ^ 2 = ηSq / (4 * (Nf + 1)) := Real.sq_sqrt (by positivity)
  have hK_bound : 4 * K ^ 2 * Nf ≤ ηSq := by
    rw [hK_sq]
    rw [show 4 * (ηSq / (4 * (Nf + 1))) * Nf = ηSq * (Nf / (Nf + 1)) by field_simp]
    have : Nf / (Nf + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  -- ── the bump with Gram ≈ B ──
  obtain ⟨χ, hχ_sm, hχ_supp, hχ_cube, hχ_gram⟩ := exists_bump_gram_approx hB hK_pos
  set F : Fin n → Fin n → (Fin n → ℝ) → ℝ :=
    fun i j y => fderiv ℝ χ y (Pi.single i 1) * fderiv ℝ χ y (Pi.single j 1) with hF
  have hχ_d : ContDiff ℝ ∞ (fun y => fderiv ℝ χ y) := hχ_sm.fderiv_right
      NashEmbedding.Sobolev.infty_add_one_le
  have hF_sm : ∀ i j, ContDiff ℝ ∞ (F i j) := fun i j =>
    (hχ_d.clm_apply contDiff_const).mul (hχ_d.clm_apply contDiff_const)
  have hF_supp : ∀ i j, HasCompactSupport (F i j) := fun i j =>
    (hχ_supp.fderiv_apply ℝ (Pi.single j 1)).mul_left
  have hF_int : ∀ i j, Integrable (cplx (F i j)) := fun i j =>
    (cplx_contDiff (hF_sm i j)).continuous.integrable_of_hasCompactSupport
      (cplx_hasCompactSupport (hF_supp i j))
  have hF_ft0 : ∀ i j, NashEmbedding.Sobolev.ftRn n (cplx (F i j)) 0 = ((gram χ i j : ℝ) : ℂ) := by
    intro i j; rw [ftRn_cplx_zero]; rfl
  -- ── choose ε ∈ (0, 1/2] with small mollifier error on every entry ──
  have h_ε := bump_mollifier_uniform_error hF_int hF_ft0 hfC_mem hηSq_pos
  obtain ⟨ε, hε_pos, hε_half, hε_bound⟩ := h_ε
  -- ── the rescaled bump and its entry kernels ──
  set χε : (Fin n → ℝ) → ℝ := rescaleBump n χ ε with hχε
  have hχε_sm : ContDiff ℝ ∞ χε := rescaleBump_contDiff hχ_sm ε
  have hχε_supp : HasCompactSupport χε := rescaleBump_hasCompactSupport hχ_supp hε_pos
  have hχε_cube : ∀ x, χε x ≠ 0 → ∀ j : Fin n, |x j| < π / 2 :=
    rescaleBump_cube hχ_cube hε_pos hε_half
  set Fε : Fin n → Fin n → (Fin n → ℝ) → ℝ :=
    fun i j y => fderiv ℝ χε y (Pi.single i 1) * fderiv ℝ χε y (Pi.single j 1) with hFε
  have hFε_eq : ∀ i j, cplx (Fε i j) = NashEmbedding.Sobolev.rescale n (cplx (F i j)) ε := by
    intro i j; funext y
    simp only [cplx, hFε, hF, NashEmbedding.Sobolev.rescale]
    rw [rescaleBump_fderiv_mul hχ_sm hε_pos i j y]
    push_cast; ring
  have hχε_d : ContDiff ℝ ∞ (fun y => fderiv ℝ χε y) := hχε_sm.fderiv_right
      NashEmbedding.Sobolev.infty_add_one_le
  have hFε_sm : ∀ i j, ContDiff ℝ ∞ (cplx (Fε i j)) := fun i j =>
    cplx_contDiff ((hχε_d.clm_apply contDiff_const).mul (hχε_d.clm_apply contDiff_const))
  have hFε_supp : ∀ i j, HasCompactSupport (cplx (Fε i j)) := fun i j =>
    cplx_hasCompactSupport (hχε_supp.fderiv_apply ℝ (Pi.single j 1)).mul_left
  have hFε_cube : ∀ i j, ∀ x, cplx (Fε i j) x ≠ 0 → ∀ l : Fin n, |x l| < π := by
    intro i j x hx l
    rw [cplx_ne_zero_iff] at hx
    have h1 : fderiv ℝ χε x (Pi.single i 1) ≠ 0 := fun h0 => hx (by simp [hFε, h0])
    exact fderiv_cube_of_half hχε_cube _ x h1 l
  have hFε_im : ∀ i j x, (cplx (Fε i j) x).im = 0 := fun i j x => cplx_im _ x
  have hFε_rd : ∀ i j, NashEmbedding.Sobolev.FTRapidDecay n (cplx (Fε i j)) := fun i j =>
    NashEmbedding.Sobolev.cinfty_rapidDecay hn (hFε_sm i j) (hFε_supp i j)
  -- ── choose M with small Riemann-sum error on every entry ──
  have h_M : ∃ M : ℕ, 0 < M ∧ ∀ i j : Fin n,
      sobolevNormSqDistrib n s
        (riemannSumDistrib n (cplx (Fε i j)) (integrationEmbed n fC) M
          - convDistrib n (cplx (Fε i j)) (integrationEmbed n fC)) < ηSq / 2 := by
    have h_each : ∀ ij : Fin n × Fin n, ∀ᶠ M : ℕ in Filter.atTop,
        sobolevNormSqDistrib n s
          (riemannSumDistrib n (cplx (Fε ij.1 ij.2)) (integrationEmbed n fC) M
            - convDistrib n (cplx (Fε ij.1 ij.2)) (integrationEmbed n fC)) < ηSq / 2 := by
      rintro ⟨i, j⟩
      exact (NashEmbedding.Sobolev.riemannSum_convergence (cplx (Fε i j)) (hFε_rd i j) hn hs
        (hu := hfC_mem)).eventually_lt_const (by positivity)
    have h_all := Filter.eventually_all.mpr h_each
    rw [Filter.eventually_atTop] at h_all
    obtain ⟨N, hN⟩ := h_all
    refine ⟨max N 1, lt_of_lt_of_le Nat.one_pos (le_max_right _ _), fun i j => ?_⟩
    exact hN _ (le_max_left _ _) ⟨i, j⟩
  obtain ⟨M, hM_pos, hM_bound⟩ := h_M
  -- ── the realization: the reindexed bump family ──
  set e : (Fin n → Fin M) ≃ Fin (Fintype.card (Fin n → Fin M)) := Fintype.equivFin _ with he
  set U0 : (Fin n → ℝ) → ((Fin n → Fin M) → ℝ) := bumpFamily n χε f M with hU0
  have hU0_sp : SmoothPeriodic U0 := bumpFamily_smoothPeriodic hχε_sm hχε_supp f M
  have hU0_d : Differentiable ℝ U0 := hU0_sp.smooth.differentiable
      NashEmbedding.Sobolev.infty_ne_zero
  set U : (Fin n → ℝ) → (Fin (Fintype.card (Fin n → Fin M)) → ℝ) :=
    fun x m => U0 x (e.symm m) with hU
  -- the defect function, entrywise
  have hdef : ∀ i j : Fin n,
      (fun x => ((dotProduct (partialDeriv i U x) (partialDeriv j U x) - (f x • B) i j : ℝ) : ℂ))
        = fun x => (((2 * π / (M : ℝ)) ^ n * ∑ k : Fin n → Fin M,
            (periodicExtension n (cplx (Fε i j)) (fun l => x l - meshPoint n M k l)).re
              * f (meshPoint n M k) - B i j * f x : ℝ) : ℂ) := by
    intro i j; funext x
    unfold partialDeriv
    rw [gram_dot_reindex e hU0_d, gram_bumpFamily hχε_sm hχε_supp hχε_cube hf0 hM_pos]
    simp only [Matrix.smul_apply, smul_eq_mul, pe]
    congr 2
    all_goals first | rfl | ring
  -- smoothness and periodicity of the defect function (real part)
  have hpe_sm : ContDiff ℝ ∞ (pe n χε) := pe_contDiff hχε_sm hχε_supp
  have hdef_sm : ∀ i j : Fin n, ContDiff ℝ ∞ (fun x : Fin n → ℝ =>
      (2 * π / (M : ℝ)) ^ n * ∑ k : Fin n → Fin M,
        (periodicExtension n (cplx (Fε i j)) (fun l => x l - meshPoint n M k l)).re
          * f (meshPoint n M k) - B i j * f x) := by
    intro i j
    have hpeF : ContDiff ℝ ∞ (fun y => (periodicExtension n (cplx (Fε i j)) y).re) :=
      Complex.reCLM.contDiff.comp
        (NashEmbedding.Sobolev.periodicExtension_contDiff (hFε_sm i j) (hFε_supp i j))
    refine ContDiff.sub (contDiff_const.mul (ContDiff.sum fun k _ => ?_))
      (contDiff_const.mul hf.smooth)
    exact (hpeF.comp (contDiff_pi.mpr fun l => (contDiff_apply ℝ ℝ l).sub contDiff_const)).mul
      contDiff_const
  have hdef_per : ∀ i j : Fin n, IsPeriodic2Pi (fun x : Fin n → ℝ =>
      (2 * π / (M : ℝ)) ^ n * ∑ k : Fin n → Fin M,
        (periodicExtension n (cplx (Fε i j)) (fun l => x l - meshPoint n M k l)).re
          * f (meshPoint n M k) - B i j * f x) := by
    intro i j x l
    simp only
    rw [hf.periodic x l]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    have : (fun m => (x + NashEmbedding.Sobolev.periodicShift n l) m - meshPoint n M k m)
        = (fun m => x m - meshPoint n M k m) + NashEmbedding.Sobolev.periodicShift n l := by
      funext m; simp; ring
    rw [this, NashEmbedding.Sobolev.periodicExtension_isPeriodic2Pi]
  refine ⟨_, U, ?_, ?_, ?_⟩
  · -- smooth periodic
    constructor
    · exact contDiff_pi.mpr fun m => (contDiff_apply ℝ ℝ (e.symm m)).comp hU0_sp.smooth
    · intro x k; funext m; simp only [hU]; rw [hU0_sp.periodic x k]
  · -- membership
    intro i j
    unfold gramDefect
    rw [hdef i j]
    exact NashEmbedding.Sobolev.smooth_periodic_memSobolevDistrib hn
      (Complex.ofRealCLM.contDiff.comp (hdef_sm i j))
      (fun x l => congrArg (fun r : ℝ => (r : ℂ)) (hdef_per i j x l)) s
  · -- the estimate
    have hentry : ∀ i j : Fin n,
        sobolevNormSqDistrib n s (gramDefect n U (fun x => f x • B) i j) < 3 * ηSq := by
      intro i j
      unfold gramDefect
      rw [hdef i j]
      have hA := hM_bound i j
      have hB' := hε_bound i j
      rw [← hFε_eq i j] at hB'
      have hmemC : MemSobolevDistrib n s (convDistrib n (cplx (Fε i j)) (integrationEmbed n fC)) :=
        NashEmbedding.Sobolev.convDistrib_memSobolevDistrib
          ((hFε_sm i j).continuous.integrable_of_hasCompactSupport (hFε_supp i j)) hfC_mem
      have hmemG : MemSobolevDistrib n s (((gram χ i j : ℝ) : ℂ) • integrationEmbed n fC) :=
        memSobolevDistrib_smul hfC_mem _
      have hmemB : MemSobolevDistrib n s (((B i j : ℝ) : ℂ) • integrationEmbed n fC) :=
        memSobolevDistrib_smul hfC_mem _
      have hC' : sobolevNormSqDistrib n s
          (((gram χ i j : ℝ) : ℂ) • integrationEmbed n fC - ((B i j : ℝ) : ℂ) • integrationEmbed
              n fC)
          ≤ K ^ 2 * Nf := by
        rw [← sub_smul, sobolevNormSqDistrib_smul]
        have h1 : ‖((gram χ i j : ℝ) : ℂ) - ((B i j : ℝ) : ℂ)‖ ≤ K := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact hχ_gram i j
        have h2 : ‖((gram χ i j : ℝ) : ℂ) - ((B i j : ℝ) : ℂ)‖ ^ 2 ≤ K ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        exact mul_le_mul_of_nonneg_right h2 hNf_nn
      have hE := NashEmbedding.Sobolev.sobolevNormSqDistrib_triangle s
        (convDistrib n (cplx (Fε i j)) (integrationEmbed n fC))
        (((gram χ i j : ℝ) : ℂ) • integrationEmbed n fC)
        (((B i j : ℝ) : ℂ) • integrationEmbed n fC)
        (hmemC.sub hmemG) (hmemG.sub hmemB)
      have hD := perEntry_residual_bound_c (M := M) hn hs (hFε_sm i j) (hFε_supp i j)
        (hFε_cube i j) (hFε_im i j) hf.smooth hf.periodic (B i j)
      -- assemble: D ≤ 2A + 2E ≤ 2A + 4B' + 4C' < ηSq + ηSq + ηSq
      have hfC' : (fun y : Fin n → ℝ => (f y : ℂ)) = fC := rfl
      rw [hfC'] at hD
      refine lt_of_le_of_lt hD ?_
      nlinarith [hA, hB', hC', hE, hK_bound]
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    calc ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (gramDefect n U (fun x => f x • B) i j)
        < ∑ i : Fin n, ∑ j : Fin n, 3 * ηSq := by
          refine Finset.sum_lt_sum_of_nonempty hne fun i _ => ?_
          exact Finset.sum_lt_sum_of_nonempty hne fun j _ => hentry i j
      _ = η ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hηSq, hnR]
          field_simp


/-! ## Finite-sum helpers for the assembly of Theorem A -/

lemma integrationEmbed_zero : integrationEmbed n (fun _ : Fin n → ℝ => (0 : ℂ)) = 0 := by
  unfold NashEmbedding.Sobolev.integrationEmbed
  have h : NashEmbedding.Sobolev.stdFourierCoeff n (fun _ : Fin n → ℝ => (0 : ℂ)) = 0 := by
    funext m; unfold NashEmbedding.Sobolev.stdFourierCoeff; simp
  rw [h, show (0 : (Fin n → ℤ) → ℂ) = (0 : ℂ) • (0 : (Fin n → ℤ) → ℂ) by simp,
    NashEmbedding.Sobolev.seqToDual_smul, zero_smul]

lemma integrationEmbed_finset_sum {ι : Type*} (t : Finset ι) (F : ι → (Fin n → ℝ) → ℝ)
    (hF : ∀ a, Continuous (F a)) :
    integrationEmbed n (fun x => ((∑ a ∈ t, F a x : ℝ) : ℂ))
      = ∑ a ∈ t, integrationEmbed n (fun x => ((F a x : ℝ) : ℂ)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [integrationEmbed_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    have h1 : (fun x => ((∑ b ∈ insert a t, F b x : ℝ) : ℂ))
        = fun x => ((F a x : ℝ) : ℂ) + ((∑ b ∈ t, F b x : ℝ) : ℂ) := by
      funext x; rw [Finset.sum_insert ha]; push_cast; ring
    rw [h1, NashEmbedding.Sobolev.integrationEmbed_add (f := fun x => ((F a x : ℝ) : ℂ))
      (g := fun x => ((∑ b ∈ t, F b x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp (hF a))
      (Complex.continuous_ofReal.comp (continuous_finsetSum _ fun b _ => hF b))]

lemma memSobolevDistrib_zero (s : ℝ) : MemSobolevDistrib n s
    (0 : NashEmbedding.Sobolev.TrigPolyDual n) := by
  unfold NashEmbedding.Sobolev.MemSobolevDistrib NashEmbedding.Sobolev.MemSobolev
  have : ∀ m, NashEmbedding.Sobolev.weight n s m * ‖fourierCoeffDistrib (0 :
      NashEmbedding.Sobolev.TrigPolyDual n) m‖ ^ 2 = 0 := by
    intro m; simp [NashEmbedding.Sobolev.fourierCoeffDistrib]
  simp_rw [this]; exact summable_zero

lemma memSobolevDistrib_add {s : ℝ} {a b : NashEmbedding.Sobolev.TrigPolyDual n}
    (ha : MemSobolevDistrib n s a) (hb : MemSobolevDistrib n s b) : MemSobolevDistrib n s (a +
        b) := by
  have hnb : MemSobolevDistrib n s (0 - b) := (memSobolevDistrib_zero s).sub hb
  rw [zero_sub] at hnb
  have := ha.sub hnb
  rwa [sub_neg_eq_add] at this

lemma memSobolevDistrib_finset_sum {ι : Type*} (t : Finset ι) {s : ℝ}
    {v : ι → NashEmbedding.Sobolev.TrigPolyDual n} (hv : ∀ a, MemSobolevDistrib n s (v a)) :
    MemSobolevDistrib n s (∑ a ∈ t, v a) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using memSobolevDistrib_zero s
  | insert a t ha ih => rw [Finset.sum_insert ha]; exact memSobolevDistrib_add (hv a) ih

/-- Cauchy–Schwarz-based finset triangle: `‖∑ᵢ vᵢ‖²_{(s)} ≤ |t| · ∑ᵢ ‖vᵢ‖²_{(s)}`.
Linear in `|t|`, tightening the naive quasi-triangle induction (which gives `2^|t|`).
Proof: `sobolevNormSqDistrib` is a genuine weighted-ℓ² Hilbert-norm-squared, so
`‖∑ᵢ v̂ᵢ(m)‖² ≤ |t| · ∑ᵢ ‖v̂ᵢ(m)‖²` pointwise in `m` by Cauchy–Schwarz
(`sq_sum_le_card_mul_sum_sq`), then integrate against the weight under `tsum`. -/
lemma sobolevNormSqDistrib_finset_sum_le {ι : Type*} (t : Finset ι) (s : ℝ)
    {v : ι → NashEmbedding.Sobolev.TrigPolyDual n} (hv : ∀ a, MemSobolevDistrib n s (v a)) :
    sobolevNormSqDistrib n s (∑ a ∈ t, v a) ≤ t.card * ∑ a ∈ t, sobolevNormSqDistrib n s (v a) := by
  classical
  -- Additivity of the Fourier coefficient functional on finite sums.
  have hfc : ∀ m, fourierCoeffDistrib (∑ a ∈ t, v a) m
      = ∑ a ∈ t, fourierCoeffDistrib (v a) m := by
    intro m
    induction t using Finset.induction_on with
    | empty => simp [NashEmbedding.Sobolev.fourierCoeffDistrib]
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, NashEmbedding.Sobolev.fourierCoeffDistrib_add, ih,
        Finset.sum_insert ha]
  -- Each `v a` contributes a summable weighted-square sequence in `m`.
  have hterm : ∀ a, Summable fun m =>
      NashEmbedding.Sobolev.weight n s m * ‖fourierCoeffDistrib (v a) m‖ ^ 2 := hv
  -- Pointwise Cauchy–Schwarz on the Fourier coefficients.
  have hptw : ∀ m,
      NashEmbedding.Sobolev.weight n s m * ‖fourierCoeffDistrib (∑ a ∈ t, v a) m‖ ^ 2
        ≤ (t.card : ℝ) * ∑ a ∈ t,
            NashEmbedding.Sobolev.weight n s m * ‖fourierCoeffDistrib (v a) m‖ ^ 2 := by
    intro m
    rw [hfc]
    have hw : (0 : ℝ) ≤ NashEmbedding.Sobolev.weight n s m :=
        NashEmbedding.Sobolev.weight_nonneg s m
    have hnorm : ‖∑ a ∈ t, fourierCoeffDistrib (v a) m‖
        ≤ ∑ a ∈ t, ‖fourierCoeffDistrib (v a) m‖ := norm_sum_le _ _
    have hsq : ‖∑ a ∈ t, fourierCoeffDistrib (v a) m‖ ^ 2
        ≤ (t.card : ℝ) * ∑ a ∈ t, ‖fourierCoeffDistrib (v a) m‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans sq_sum_le_card_mul_sum_sq
    calc NashEmbedding.Sobolev.weight n s m * ‖∑ a ∈ t, fourierCoeffDistrib (v a) m‖ ^ 2
        ≤ NashEmbedding.Sobolev.weight n s m *
            ((t.card : ℝ) * ∑ a ∈ t, ‖fourierCoeffDistrib (v a) m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hw
      _ = (t.card : ℝ) * ∑ a ∈ t,
            NashEmbedding.Sobolev.weight n s m * ‖fourierCoeffDistrib (v a) m‖ ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun a _ => by ring)
  -- LHS summable = MemSobolevDistrib of the finite sum.
  have hLHS : Summable fun m =>
      NashEmbedding.Sobolev.weight n s m * ‖fourierCoeffDistrib (∑ a ∈ t, v a) m‖ ^ 2 :=
    memSobolevDistrib_finset_sum t hv
  -- RHS summable: constant times a finite sum of summables.
  have hRHS_inner : Summable fun m => ∑ a ∈ t,
      NashEmbedding.Sobolev.weight n s m * ‖fourierCoeffDistrib (v a) m‖ ^ 2 :=
    summable_sum (fun a _ => hterm a)
  have hRHS : Summable fun m => (t.card : ℝ) * ∑ a ∈ t,
      NashEmbedding.Sobolev.weight n s m * ‖fourierCoeffDistrib (v a) m‖ ^ 2 :=
    hRHS_inner.mul_left _
  have hle := Summable.tsum_le_tsum hptw hLHS hRHS
  -- Convert the RHS tsum to `t.card * ∑ a ∈ t, sobolevNormSqDistrib n s (v a)`.
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun a _ => hterm a)] at hle
  exact hle

/-- Gram entries of a sigma-indexed concatenation are sums of the Gram entries. -/
lemma gram_dot_sigma {A : Type*} [Fintype A] {N : A → ℕ}
    {U : (a : A) → (Fin n → ℝ) → (Fin (N a) → ℝ)} (hU : ∀ a, Differentiable ℝ (U a))
    (v w : Fin n → ℝ) (x : Fin n → ℝ) :
    dotProduct (fderiv ℝ (fun x (p : Σ a, Fin (N a)) => U p.1 x p.2) x v)
        (fderiv ℝ (fun x (p : Σ a, Fin (N a)) => U p.1 x p.2) x w)
      = ∑ a, dotProduct (fderiv ℝ (U a) x v) (fderiv ℝ (U a) x w) := by
  have hcomp : ∀ (a : A) (k : Fin (N a)), HasFDerivAt (fun x => U a x k)
      ((ContinuousLinearMap.proj k).comp (fderiv ℝ (U a) x)) x :=
    fun a k => hasFDerivAt_pi'.mp (hU a x).hasFDerivAt k
  have hf : HasFDerivAt (fun x (p : Σ a, Fin (N a)) => U p.1 x p.2)
      (ContinuousLinearMap.pi fun p : Σ a, Fin (N a) =>
        (ContinuousLinearMap.proj p.2).comp (fderiv ℝ (U p.1) x)) x :=
    hasFDerivAt_pi.mpr fun p => hcomp p.1 p.2
  rw [hf.fderiv]
  unfold dotProduct
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  rw [Fintype.sum_sigma]

/-! ## Theorem A -/

/-- Concatenation-Gram identity: the Gram entries of a `Fintype.equivFin`-reindexed
sigma-concatenation of smooth vector-valued maps are the pointwise sum of the Gram
entries of the factors. -/
lemma concat_dotProduct_partialDeriv
    {A : Type*} [Fintype A] {N_k : A → ℕ}
    {U_k : (a : A) → (Fin n → ℝ) → (Fin (N_k a) → ℝ)}
    (hU : ∀ a, ContDiff ℝ ∞ (U_k a))
    (e : (Σ a, Fin (N_k a)) ≃ Fin (Fintype.card (Σ a, Fin (N_k a))))
    (i j : Fin n) (x : Fin n → ℝ) :
    dotProduct
        (partialDeriv i
          (fun y (m : Fin (Fintype.card (Σ a, Fin (N_k a)))) =>
            U_k (e.symm m).1 y (e.symm m).2) x)
        (partialDeriv j
          (fun y m => U_k (e.symm m).1 y (e.symm m).2) x)
      = ∑ a : A, dotProduct (partialDeriv i (U_k a) x) (partialDeriv j (U_k a) x) := by
  have hU_a_diff : ∀ a, Differentiable ℝ (U_k a) :=
    fun a => (hU a).differentiable NashEmbedding.Sobolev.infty_ne_zero
  have hU_sigma_cd : ContDiff ℝ ∞ (fun y (p : Σ a, Fin (N_k a)) => U_k p.1 y p.2) := by
    refine contDiff_pi.mpr fun p => ?_
    exact contDiff_pi.mp (hU p.1) p.2
  have hU_sigma_diff : Differentiable ℝ (fun y (p : Σ a, Fin (N_k a)) => U_k p.1 y p.2) :=
    hU_sigma_cd.differentiable NashEmbedding.Sobolev.infty_ne_zero
  unfold partialDeriv
  rw [gram_dot_reindex e hU_sigma_diff]
  exact gram_dot_sigma hU_a_diff _ _ _

/-- The squared Sobolev norm of a finite sum plus a remainder has a cardinality bound. -/
private theorem sobolevNormSqDistrib_sum_add_le {A : Type*} [Fintype A] (s : ℝ)
    (v : A → NashEmbedding.Sobolev.TrigPolyDual n) (w : NashEmbedding.Sobolev.TrigPolyDual n)
    (hv : ∀ a, MemSobolevDistrib n s (v a)) (hw : MemSobolevDistrib n s w) :
    sobolevNormSqDistrib n s ((∑ a, v a) + w) ≤
      2 * (Fintype.card A * ∑ a, sobolevNormSqDistrib n s (v a)) +
        2 * sobolevNormSqDistrib n s w := by
  have hsum := sobolevNormSqDistrib_finset_sum_le Finset.univ s hv
  simp only [Finset.card_univ] at hsum
  have htri := NashEmbedding.Sobolev.sobolevNormSqDistrib_triangle s ((∑ a, v a) + w) w 0
    (by simpa only [add_sub_cancel_right] using memSobolevDistrib_finset_sum Finset.univ hv)
    (by simpa only [sub_zero] using hw)
  simp only [add_sub_cancel_right, sub_zero] at htri
  linarith

/-- **Theorem A** (`2s > n`): every smooth metric is an `H^s`-limit of realizable ones. -/
theorem realizable_approx (hn : 0 < n) {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsSmoothMetric g) {s : ℝ} (hs : (n : ℝ) < 2 * s) {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (u : (Fin n → ℝ) → (Fin N → ℝ)), SmoothPeriodic u ∧
      (∀ i j, MemSobolevDistrib n s (gramDefect n u g i j)) ∧
      ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (gramDefect n u g i j) < η ^ 2 := by
  classical
  have hη_half : (0 : ℝ) < η / 2 := by positivity
  obtain ⟨M, hM_pos, f, B, hf_sp, hf_nn, hB_psd, hres_mem, hres_bound⟩ :=
    convex_combination_approx hn hg hs hη_half
  set Mn : ℝ := (M : ℝ) ^ n with hMn_def
  have hMn_pos : 0 < Mn := by rw [hMn_def]; positivity
  have hη_k_pos : (0 : ℝ) < η / (4 * Mn) := by positivity
  choose N_k U_k hU_sp hU_mem hU_bound using fun k : Fin n → Fin M =>
    realize_fB hn (hf_sp k) (hf_nn k) (hB_psd k) hs hη_k_pos
  set N' : ℕ := Fintype.card (Σ k : Fin n → Fin M, Fin (N_k k)) with hN'_def
  let e : (Σ k : Fin n → Fin M, Fin (N_k k)) ≃ Fin N' := Fintype.equivFin _
  let u : (Fin n → ℝ) → Fin N' → ℝ :=
    fun x m => U_k (e.symm m).1 x (e.symm m).2
  have hg_cd : ∀ i j : Fin n, ContDiff ℝ ∞ (fun x => g x i j) := fun i j =>
    contDiff_pi.mp (contDiff_pi.mp hg.smoothPeriodic.smooth i) j
  have hf_cd : ∀ k : Fin n → Fin M, ContDiff ℝ ∞ (f k) := fun k => (hf_sp k).smooth
  have hU_k_pd_cd : ∀ k i, ContDiff ℝ ∞ (partialDeriv i (U_k k)) := fun k i =>
    ((hU_sp k).1.fderiv_right NashEmbedding.Sobolev.infty_add_one_le).clm_apply contDiff_const
  have hU_k_pd_dot_cd : ∀ k i j,
      ContDiff ℝ ∞ (fun x => partialDeriv i (U_k k) x ⬝ᵥ partialDeriv j (U_k k) x) := by
    intro k i j
    refine ContDiff.sum ?_
    intro l _
    exact (contDiff_pi.mp (hU_k_pd_cd k i) l).mul (contDiff_pi.mp (hU_k_pd_cd k j) l)
  set D : (Fin n → Fin M) → Fin n → Fin n → NashEmbedding.Sobolev.TrigPolyDual n :=
    fun k i j => gramDefect n (U_k k) (fun y => f k y • B k) i j with hD_def
  set R : Fin n → Fin n → NashEmbedding.Sobolev.TrigPolyDual n :=
    fun i j => integrationEmbed n
      (fun x => (((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j : ℝ) : ℂ)) with hR_def
  have hsplit : ∀ i j : Fin n,
      gramDefect n u g i j = (∑ k : Fin n → Fin M, D k i j) + R i j := by
    intro i j
    have hpt : ∀ x : Fin n → ℝ,
        (((partialDeriv i u x ⬝ᵥ partialDeriv j u x) - g x i j : ℝ) : ℂ)
          = (((∑ k : Fin n → Fin M,
                (partialDeriv i (U_k k) x ⬝ᵥ partialDeriv j (U_k k) x -
                  f k x * B k i j)) +
              ((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j) : ℝ) : ℂ) := by
      intro x
      congr 1
      have hconcat := concat_dotProduct_partialDeriv (fun k => (hU_sp k).1) e i j x
      rw [hconcat]
      rw [Finset.sum_sub_distrib]
      ring
    have hgd : gramDefect n u g i j
        = integrationEmbed n (fun x =>
            (((∑ k : Fin n → Fin M,
                (partialDeriv i (U_k k) x ⬝ᵥ partialDeriv j (U_k k) x -
                  f k x * B k i j)) +
              ((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j) : ℝ) : ℂ)) := by
      unfold gramDefect
      congr 1
      funext x
      exact hpt x
    rw [hgd]
    have hcont_a : Continuous (fun x : Fin n → ℝ =>
        (((∑ k : Fin n → Fin M,
            (partialDeriv i (U_k k) x ⬝ᵥ partialDeriv j (U_k k) x -
              f k x * B k i j)) : ℝ) : ℂ)) := by
      refine Complex.continuous_ofReal.comp ?_
      refine continuous_finsetSum _ ?_
      intro k _
      exact ((hU_k_pd_dot_cd k i j).sub ((hf_cd k).mul contDiff_const)).continuous
    have hcont_b : Continuous (fun x : Fin n → ℝ =>
        (((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j : ℝ) : ℂ)) := by
      refine Complex.continuous_ofReal.comp ?_
      refine Continuous.sub ?_ (hg_cd i j).continuous
      refine continuous_finsetSum _ ?_
      intro k _
      exact ((hf_cd k).mul contDiff_const).continuous
    have h_add_split : integrationEmbed n (fun x =>
          (((∑ k : Fin n → Fin M,
              (partialDeriv i (U_k k) x ⬝ᵥ partialDeriv j (U_k k) x -
                f k x * B k i j)) +
            ((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j) : ℝ) : ℂ))
        = integrationEmbed n (fun x =>
            (((∑ k : Fin n → Fin M,
                (partialDeriv i (U_k k) x ⬝ᵥ partialDeriv j (U_k k) x -
                  f k x * B k i j)) : ℝ) : ℂ))
          + integrationEmbed n (fun x =>
            (((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j : ℝ) : ℂ)) := by
      have h_eq : (fun x : Fin n → ℝ =>
          (((∑ k : Fin n → Fin M,
              (partialDeriv i (U_k k) x ⬝ᵥ partialDeriv j (U_k k) x -
                f k x * B k i j)) +
            ((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j) : ℝ) : ℂ))
          = fun x =>
            (((∑ k : Fin n → Fin M,
                (partialDeriv i (U_k k) x ⬝ᵥ partialDeriv j (U_k k) x -
                  f k x * B k i j)) : ℝ) : ℂ)
            + (((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j : ℝ) : ℂ) := by
        funext x; push_cast; ring
      rw [h_eq, NashEmbedding.Sobolev.integrationEmbed_add hcont_a hcont_b]
    rw [h_add_split]
    have h_finset_sum : integrationEmbed n (fun x =>
          (((∑ k : Fin n → Fin M,
              (partialDeriv i (U_k k) x ⬝ᵥ partialDeriv j (U_k k) x -
                f k x * B k i j)) : ℝ) : ℂ))
        = ∑ k : Fin n → Fin M, integrationEmbed n (fun x =>
            (((partialDeriv i (U_k k) x ⬝ᵥ partialDeriv j (U_k k) x -
              f k x * B k i j) : ℝ) : ℂ)) :=
      integrationEmbed_finset_sum _ _
        (fun k => ((hU_k_pd_dot_cd k i j).sub ((hf_cd k).mul contDiff_const)).continuous)
    rw [h_finset_sum]
    have h_D_form : ∀ k : Fin n → Fin M,
        integrationEmbed n (fun x =>
          (((partialDeriv i (U_k k) x ⬝ᵥ partialDeriv j (U_k k) x -
            f k x * B k i j) : ℝ) : ℂ))
        = D k i j := by
      intro k
      change integrationEmbed n _ = gramDefect n (U_k k) (fun y => f k y • B k) i j
      unfold gramDefect
      congr 1
    simp_rw [h_D_form]
    rfl
  have hD_mem : ∀ k i j, MemSobolevDistrib n s (D k i j) := fun k i j => hU_mem k i j
  have hR_mem : ∀ i j, MemSobolevDistrib n s (R i j) := fun i j => hres_mem i j
  have hsum_D_mem : ∀ i j, MemSobolevDistrib n s (∑ k : Fin n → Fin M, D k i j) := fun i j =>
    memSobolevDistrib_finset_sum _ (fun k => hD_mem k i j)
  refine ⟨N', u, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine contDiff_pi.mpr fun m => ?_
      exact contDiff_pi.mp (hU_sp (e.symm m).1).1 (e.symm m).2
    · intro x l
      funext m
      exact congrFun ((hU_sp (e.symm m).1).2 x l) (e.symm m).2
  · intro i j
    rw [hsplit i j]
    exact memSobolevDistrib_add (hsum_D_mem i j) (hR_mem i j)
  · have hcard : ((Finset.univ : Finset (Fin n → Fin M)).card : ℝ) = Mn := by
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hMn_def,
        Nat.cast_pow]
    have h_per_ij : ∀ i j : Fin n,
        sobolevNormSqDistrib n s (gramDefect n u g i j)
          ≤ 2 * (Mn * ∑ k : Fin n → Fin M, sobolevNormSqDistrib n s (D k i j))
            + 2 * sobolevNormSqDistrib n s (R i j) := by
      intro i j
      rw [hsplit i j]
      have h := sobolevNormSqDistrib_sum_add_le s (fun k => D k i j) (R i j)
        (fun k => hD_mem k i j) (hR_mem i j)
      simpa only [Finset.card_univ] using hcard ▸ h
    have hS : ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (gramDefect n u g i j)
        ≤ 2 * Mn * ∑ i : Fin n, ∑ j : Fin n,
            (∑ k : Fin n → Fin M, sobolevNormSqDistrib n s (D k i j))
          + 2 * ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (R i j) := by
      calc ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (gramDefect n u g i j)
          ≤ ∑ i : Fin n, ∑ j : Fin n,
              (2 * (Mn * ∑ k : Fin n → Fin M, sobolevNormSqDistrib n s (D k i j))
                + 2 * sobolevNormSqDistrib n s (R i j)) :=
                Finset.sum_le_sum fun i _ =>
                  Finset.sum_le_sum fun j _ => h_per_ij i j
        _ = 2 * Mn * ∑ i : Fin n, ∑ j : Fin n,
                (∑ k : Fin n → Fin M, sobolevNormSqDistrib n s (D k i j))
            + 2 * ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (R i j) := by
              simp only [Finset.mul_sum, Finset.sum_add_distrib]
              ring
    have hswap : ∑ i : Fin n, ∑ j : Fin n,
          (∑ k : Fin n → Fin M, sobolevNormSqDistrib n s (D k i j))
        = ∑ k : Fin n → Fin M, ∑ i : Fin n, ∑ j : Fin n,
            sobolevNormSqDistrib n s (D k i j) := by
      have h1 : (∑ i : Fin n, ∑ j : Fin n,
            ∑ k : Fin n → Fin M, sobolevNormSqDistrib n s (D k i j))
          = ∑ i : Fin n, ∑ k : Fin n → Fin M, ∑ j : Fin n,
              sobolevNormSqDistrib n s (D k i j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
      rw [h1, Finset.sum_comm]
    rw [hswap] at hS
    have hDbnd : ∀ k, ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (D k i j)
          < (η / (4 * Mn)) ^ 2 := fun k => hU_bound k
    have hDbnd_sum : ∑ k : Fin n → Fin M, ∑ i : Fin n, ∑ j : Fin n,
          sobolevNormSqDistrib n s (D k i j) ≤ Mn * (η / (4 * Mn)) ^ 2 := by
      calc ∑ k : Fin n → Fin M, ∑ i : Fin n, ∑ j : Fin n,
              sobolevNormSqDistrib n s (D k i j)
          ≤ ∑ k : Fin n → Fin M, (η / (4 * Mn)) ^ 2 :=
            Finset.sum_le_sum fun k _ => (hDbnd k).le
        _ = Mn * (η / (4 * Mn)) ^ 2 := by
            rw [Finset.sum_const, ← hcard]
            simp [nsmul_eq_mul]
    have hRbnd : ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (R i j) < (η / 2) ^ 2 :=
      hres_bound
    have hFinal :
        2 * Mn * (Mn * (η / (4 * Mn)) ^ 2) + 2 * (η / 2) ^ 2 < η ^ 2 := by
      have hMn_ne : Mn ≠ 0 := ne_of_gt hMn_pos
      have hkey : 2 * Mn * (Mn * (η / (4 * Mn)) ^ 2) = η ^ 2 / 8 := by
        field_simp
        ring
      rw [hkey]
      nlinarith [sq_nonneg η, hη]
    calc ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (gramDefect n u g i j)
        ≤ 2 * Mn * (∑ k : Fin n → Fin M, ∑ i : Fin n, ∑ j : Fin n,
              sobolevNormSqDistrib n s (D k i j))
          + 2 * ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (R i j) := hS
      _ ≤ 2 * Mn * (Mn * (η / (4 * Mn)) ^ 2) + 2 * (η / 2) ^ 2 := by gcongr
      _ < η ^ 2 := hFinal

/-- **Theorem A** for every real `s`. -/
theorem realizable_approx_all_s (hn : 0 < n) {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsSmoothMetric g) (s : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (u : (Fin n → ℝ) → (Fin N → ℝ)), SmoothPeriodic u ∧
      (∀ i j, MemSobolevDistrib n s (gramDefect n u g i j)) ∧
      ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (gramDefect n u g i j) < η ^ 2 := by
  set t : ℝ := max s ((n : ℝ) + 1) with ht_def
  have hst : s ≤ t := le_max_left _ _
  have ht_ge : (n : ℝ) + 1 ≤ t := le_max_right _ _
  have ht : (n : ℝ) < 2 * t := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  obtain ⟨N, u, hu_sp, hu_mem, hu_bound⟩ := realizable_approx hn hg ht hη
  refine ⟨N, u, hu_sp, ?_, ?_⟩
  · intro i j; exact (hu_mem i j).mono hst
  · calc ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n s (gramDefect n u g i j)
        ≤ ∑ i : Fin n, ∑ j : Fin n, sobolevNormSqDistrib n t (gramDefect n u g i j) :=
          Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ =>
              NashEmbedding.Sobolev.sobolevNormSqDistrib_mono (hu_mem i j) hst
      _ < η ^ 2 := hu_bound

end NashEmbedding

end
