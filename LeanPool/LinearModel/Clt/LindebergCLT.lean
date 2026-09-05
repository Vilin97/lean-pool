/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import LeanPool.LinearModel.Clt.ProductExpLimit
import LeanPool.LinearModel.Clt.TaylorErrorBound
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.IdentDistrib

/-!
# The Lindeberg Central Limit Theorem

This file establishes the Lindeberg Central Limit Theorem, first for a triangular array `X_{n,k}`
of row-wise independent, mean-zero random variables, then for a sequence `(Xₖ)` of independent
mean-zero random variables.

Given a triangular array `(X_{n,k})`, we define `σ_{n,k}² = E[X_{n,k}²]`, `sₙ² = ∑ₖ σ_{n,k}²`
and `Sₙ = ∑ₖ X_{n,k}`. The Lindeberg condition then states that for all `ε > 0`,
`(1/sₙ²) ∑ₖ ∫_{|X_{n,k}| > εsₙ} X_{n,k}² dP → 0`. We make analogous definitions
for the sequence case.

The main results are the following (note that all require some additional standard assumptions on
integrability and measurability, and also that the sum `sₙ²` described above is eventually
non-zero):

· `Feller_negligibility_of_Lindeberg_Triangular`/`Feller_negligibility_of_Lindeberg` - if the
  Lindeberg condition holds then `max σ_{n,k}² / sₙ² → 0` as `n → ∞`.
· `central_limit_charFun_Lindeberg_Triangular`/`central_limit_charFun_Lindeberg` - if the Lindeberg
  condition holds then the characteristic function of `Sₙ/sₙ` converges pointwise to `exp(-t²/2)`.
· `central_limit_Lindeberg_Triangular`/`central_limit_Lindeberg` - if the Lindeberg condition holds
  then `Sₙ / sₙ` converges in distribution to `N(0,1)` (obtained by combining the characteristic
  function statement with the Lévy convergence theorem).

In each case the sequence-specific results are derived from the triangular versions
by specializing to the constant array `X_{n,k} := Xₖ`.
-/

namespace LeanPool.LinearModel

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Finset
open scoped Real Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


section TriangularArrayDefinitions

/-- The standard real Gaussian `𝓝 (0, 1)`. -/
abbrev stdGaussian : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

/-- The sum of moments `sₙ² = ∑ₖ σ_{n,k}²` (assuming random variables `X_{n,k}` are mean-zero) -/
abbrev momentSumTriangular (X : (n : ℕ) → Fin n → Ω → ℝ) (P : Measure Ω) (n : ℕ) : ℝ :=
  ∑ k, P[(X n k) ^ 2]

/-- The domain of integration `{|X_{n,k}| > εsₙ}` appearing in the Lindeberg condition -/
def LindebergSetTriangular (X : (n : ℕ) → Fin n → Ω → ℝ) (P : Measure Ω) {n : ℕ} (k : Fin n)
    (ε : ℝ) : Set Ω :=
  {ω | ε * √ (momentSumTriangular X P n) < |X n k ω|}

/-- The Lindeberg condition (triangular array): for all `ε > 0`,
`(1/sₙ²) ∑ₖ ∫_{|X_{n,k}| > εsₙ} X_{n,k}² dP → 0`. -/
def LindebergConditionTriangular (X : (n : ℕ) → Fin n → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ ε > (0 : ℝ), Tendsto (fun n ↦
     (1 / momentSumTriangular X P n) *
       ∑ k, ∫ ω in (LindebergSetTriangular X P k ε), (X n k ω) ^ 2 ∂P) atTop (𝓝 0)

/-- The normalized partial sum: `Sₙ/sₙ = (Σₖ X_{n,k})/sₙ`. -/
abbrev LindebergSumTriangular (X : (n : ℕ) → Fin n → Ω → ℝ) (P : Measure Ω) (n : ℕ) (ω : Ω) : ℝ :=
   (∑ k : Fin n, X n k ω) / (√(momentSumTriangular X P n))

end TriangularArrayDefinitions


section IntermediateResults

/-- `Sₙ/sₙ` is a.e.-measurable — needed to form its pushforward probability measure. -/
lemma aemeasurable_LindebergSumTriangular {X : (n : ℕ) → Fin n → Ω → ℝ} {μ : Measure Ω} (n : ℕ)
    (hX_meas : ∀ n (k : Fin n), Measurable (X n k)) :
    AEMeasurable (LindebergSumTriangular X μ n) μ := by fun_prop

/-- The characteristic function of `Sₙ/sₙ` factors as `∏ₖ φ_{X_{n,k}}(t/sₙ)`. -/
lemma charFun_LindebergSumTriangular {X : (n : ℕ) → Fin n → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hX_meas : ∀ n k, Measurable (X n k))
    (hX_ind : ∀ n, iIndepFun (X n) P)
    {n : ℕ} {t : ℝ} :
    charFun (P.map (LindebergSumTriangular X P n)) t =
      ∏ k : Fin n, charFun (P.map (X n k)) (t / √ (momentSumTriangular X P n)) := by
  have hpush : P.map (LindebergSumTriangular X P n) =
      ((P.map (fun ω (k : Fin n) ↦ X n k ω)).map (fun x ↦ ∑ k, x k)).map
      (· / √ (momentSumTriangular X P n)) := by
    repeat rw [Measure.map_map]
    · rfl
    all_goals fun_prop
  -- Row-wise independence directly gives the product measure factoring
  have hpi_map := (iIndepFun_iff_map_fun_eq_pi_map
    fun k : Fin n ↦ (hX_meas n k).aemeasurable).mp (hX_ind n)
  have inst k := P.isProbabilityMeasure_map (hX_meas n k).aemeasurable
  simp_rw [hpush, hpi_map, div_eq_inv_mul, charFun_map_mul, charFun_map_sum_pi_eq_prod]
  simp

/-- Rewrite charFun of pushforward of a generic measure as integral over original space. -/
lemma charFun_map_eq_integral {P : Measure Ω}
    (Y : Ω → ℝ) (hY_meas : Measurable Y) (t : ℝ) :
    charFun (P.map Y) t = ∫ ω, cexp ((t * Y ω) * I) ∂P := by
  rw [charFun_apply_real, integral_map hY_meas.aemeasurable (by fun_prop)]

/-- `‖exp(ix) - 1 - ix‖ ≤ |x|² / 2` for all `x ∈ ℝ`. -/
private lemma norm_cexp_mul_I_sub_taylor_1 (x : ℝ) :
  ‖cexp (x * I) - 1 - x * I‖ ≤ |x| ^ 2 / 2 := by
    rw [← sub_add_eq_sub_sub]
    have hsum : ∑ k ∈ range 2, (x * I) ^ k / k.factorial = 1 + x * I := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]; simp
    rw [← hsum]
    exact norm_cexp_mul_I_sub_taylor_le 2 x

/-- `‖exp(ix) - 1 - ix + x² / 2‖ ≤ x²` for all `x ∈ ℝ`. -/
private lemma norm_cexp_mul_I_bound_sub_taylor_2_quadratic (x : ℝ) :
  ‖cexp (x * I) - 1 - x * I + x ^ 2 / 2‖ ≤ x ^ 2 := by
  calc
    ‖cexp (x * I) - 1 - x * I + x ^ 2 / 2‖
        ≤ ‖cexp (x * I) - 1 - x * I‖ + ‖(x : ℂ) ^ 2 / 2‖ := by
      apply norm_add_le (cexp (x * I) - 1 - x * I) (x ^ 2 / 2)
    _ ≤ |x| ^ 2 / 2 + ‖(x : ℂ) ^ 2 / 2‖ := by
      apply add_le_add (norm_cexp_mul_I_sub_taylor_1 _) (by linarith)
    _ ≤ x ^ 2 := by norm_num

/-- `‖exp(ix) - 1 - ix + x² / 2‖ ≤ |x|³ / 6` for all `y ∈ ℝ`. -/
private lemma norm_cexp_mul_I_bound_sub_taylor_2_cubic (x : ℝ) :
  ‖cexp (x * I) - 1 - x * I + x ^ 2 / 2‖ ≤ |x| ^ 3 / 6 := by
    rw [← sub_add_eq_sub_sub]
    have hsum : ∑ k ∈ range 3, (x * I) ^ k / k.factorial = 1 + x * I - x ^ 2 / 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      simp [mul_pow, Complex.I_sq]; ring
    rw [sub_add, ← hsum]
    exact norm_cexp_mul_I_sub_taylor_le 3 x

section TaylorRemainderIntegrals

variable {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

/-- The first-order Taylor remainder `exp(iuX) − 1 − iuX` is integrable when `X` is. -/
private lemma integrable_cexp_remainder_one (hX_meas : Measurable X)
    (hX_int : Integrable X P) (u : ℝ) :
    Integrable (fun ω => cexp (↑(u * X ω) * I) - 1 - ↑(u * X ω) * I) P := by
  have hexp_int : Integrable (fun ω => cexp (↑(u * X ω) * I)) P := by
    exact_mod_cast (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (ae_of_all _ fun ω => le_of_eq (norm_exp_ofReal_mul_I (u * X ω)))
  have huXI_int : Integrable (fun ω => ((u * X ω : ℝ) : ℂ) * I) P :=
    ((hX_int.const_mul u).ofReal).mul_const I
  exact_mod_cast (hexp_int.sub (integrable_const (1 : ℂ))).sub huXI_int

/-- The second-order Taylor remainder `exp(iuX) − 1 − iuX + (uX)²/2` is integrable
when `X ∈ L²`. -/
private lemma integrable_cexp_remainder_two (hX_meas : Measurable X)
    (hX_MemL2 : MemLp X 2 P) (u : ℝ) :
    Integrable (fun ω => cexp (↑(u * X ω) * I) - 1 - ↑(u * X ω) * I
      + ((u * X ω) ^ 2 / 2)) P := by
  have hsq : Integrable (fun ω => (u * X ω) ^ 2 / 2) P :=
    (hX_MemL2.integrable_sq.const_mul (u ^ 2 / 2)).congr (ae_of_all _ fun ω => by ring)
  exact_mod_cast
    (integrable_cexp_remainder_one hX_meas (hX_MemL2.integrable one_le_two) u).add hsq.ofReal

/-- For a centered integrable `X`, `φ_X(u) − 1` is the integral of the first-order
Taylor remainder of `exp(iuX)`. -/
private lemma charFun_sub_one_eq_integral_remainder (hX_meas : Measurable X)
    (hX_centred : P[X] = 0) (hX_int : Integrable X P) (u : ℝ) :
    charFun (P.map X) u - 1 =
      ∫ ω, (cexp (↑(u * X ω) * I) - 1 - ↑(u * X ω) * I) ∂P := by
  have hexp_int : Integrable (fun ω => cexp (↑(u * X ω) * I)) P := by
    exact_mod_cast (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (ae_of_all _ fun ω => le_of_eq (norm_exp_ofReal_mul_I (u * X ω)))
  have huXI_int : Integrable (fun ω => ((u * X ω : ℝ) : ℂ) * I) P :=
    ((hX_int.const_mul u).ofReal).mul_const I
  rw [charFun_map_eq_integral X hX_meas u]
  have hsplit :
      ∫ ω, (cexp (↑(u * X ω) * I) - 1 - ↑(u * X ω) * I) ∂P =
        (∫ ω, cexp ((u * X ω) * I) ∂P) - 1 - (∫ ω, ((u * X ω)) * I ∂P) := by
    have h2 : (∫ ω, (cexp (↑(u * X ω) * I) - 1 - ↑(u * X ω) * I) ∂P) =
        (∫ ω, (cexp (↑(u * X ω) * I) - 1) ∂P) - (∫ ω, ((u * X ω : ℝ) : ℂ) * I ∂P) :=
      integral_sub (hexp_int.sub (integrable_const _)) huXI_int
    have h3 : (∫ ω, (cexp (↑(u * X ω) * I) - 1) ∂P) =
        (∫ ω, cexp (↑(u * X ω) * I) ∂P) - (∫ _ω, (1 : ℂ) ∂P) :=
      integral_sub hexp_int (integrable_const _)
    rw [h2, h3, integral_const]; simp
  have hlin : ∫ ω, (u * X ω) * I ∂P = 0 := by
    rw [integral_mul_const, integral_const_mul, integral_complex_ofReal, hX_centred]; norm_num
  rw [hsplit, hlin]; norm_num

/-- For a centered `L²` variable, `φ_X(u) − 1 + u²·E[X²]/2` is the integral of the
second-order Taylor remainder of `exp(iuX)`. -/
private lemma charFun_sub_one_add_eq_integral_remainder (hX_meas : Measurable X)
    (hX_centred : P[X] = 0) (hX_MemL2 : MemLp X 2 P) (u : ℝ) :
    charFun (P.map X) u - 1 + (u ^ 2 * P[X ^ 2] / 2 : ℝ) =
      ∫ ω, (cexp (↑(u * X ω) * I) - 1 - ↑(u * X ω) * I + ((u * X ω) ^ 2 / 2)) ∂P := by
  have hsq : Integrable (fun ω => (u * X ω) ^ 2 / 2) P :=
    (hX_MemL2.integrable_sq.const_mul (u ^ 2 / 2)).congr (ae_of_all _ fun ω => by ring)
  have hq : ∫ ω, (((u * X ω) ^ 2 / 2 : ℝ) : ℂ) ∂P = ((u ^ 2 * P[X ^ 2] / 2 : ℝ) : ℂ) := by
    rw [integral_complex_ofReal]
    norm_cast
    rw [show (fun ω => (u * X ω) ^ 2 / 2) = fun ω => (u ^ 2 / 2) * X ω ^ 2 from
      funext fun ω => by ring, integral_const_mul]
    simp only [Pi.pow_apply]
    ring
  have hsqC : Integrable (fun ω => (((u * X ω) ^ 2 / 2 : ℝ) : ℂ)) P := hsq.ofReal
  calc charFun (P.map X) u - 1 + (u ^ 2 * P[X ^ 2] / 2 : ℝ)
      = (∫ ω, (cexp (↑(u * X ω) * I) - 1 - ↑(u * X ω) * I) ∂P)
        + ∫ ω, (((u * X ω) ^ 2 / 2 : ℝ) : ℂ) ∂P := by
        rw [charFun_sub_one_eq_integral_remainder hX_meas hX_centred
          (hX_MemL2.integrable one_le_two) u, hq]
    _ = ∫ ω, (cexp (↑(u * X ω) * I) - 1 - ↑(u * X ω) * I
          + (((u * X ω) ^ 2 / 2 : ℝ) : ℂ)) ∂P :=
        (integral_add (integrable_cexp_remainder_one hX_meas
          (hX_MemL2.integrable one_le_two) u) hsqC).symm
    _ = ∫ ω, (cexp (↑(u * X ω) * I) - 1 - ↑(u * X ω) * I + ((u * X ω) ^ 2 / 2)) ∂P := by
        push_cast
        rfl

end TaylorRemainderIntegrals

/-- Under the Lindeberg condition, `∑ₖ (φ_{X_{n,k}}(t/sₙ) - 1 + σ_{n,k}² * t² /(2sₙ²)) → 0`. -/
private lemma tendsto_sum_charFun_sub_add {X : (n : ℕ) → Fin n → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hX_meas : ∀ n k, Measurable (X n k))
    (hX_centred : ∀ n k, P[X n k] = 0)
    (hX_MemL2 : ∀ n k, MemLp (X n k) 2 P)
    (hLind : LindebergConditionTriangular X P)
    (hmSum_pos : ∀ᶠ n in atTop, 0 < momentSumTriangular X P n)
    (t : ℝ) :
    Tendsto (fun n ↦ ∑ k : Fin n,
      (charFun (P.map (X n k)) (t / √(momentSumTriangular X P n)) - 1
        + (P[(X n k) ^ 2] * t ^ 2 / (2 * momentSumTriangular X P n)))) atTop (𝓝 0) := by
  by_cases ht : t = 0
  · subst ht
    have hzero : ∀ n, ∀ k, charFun (P.map (X n k)) (0 / √(momentSumTriangular X P n)) - 1
            + P[(X n k) ^ 2] * 0 ^ 2 / (2 * momentSumTriangular X P n) = 0 := by
      intro n k
      simp [P.isProbabilityMeasure_map (hX_meas n k).aemeasurable]
    exact tendsto_const_nhds.congr fun n => (Finset.sum_eq_zero fun k _ => hzero n k).symm
  have ht_abs : 0 < |t| := abs_pos.mpr ht
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set ε := min (1 / |t|) (δ / (2 * (|t| ^ 3 + 1))) with hε_def
  have hε_pos : 0 < ε := lt_min (by positivity) (by positivity)
  have hε_t : ε * |t| ≤ 1 := by
    have h : ε ≤ 1 / |t| := min_le_left _ _
    calc ε * |t| ≤ (1 / |t|) * |t| := by gcongr
      _ = 1 := by field_simp
  have hε_t3 : ε * |t| ^ 3 ≤ δ / 2 := by
    have h : ε ≤ δ / (2 * (|t| ^ 3 + 1)) := min_le_right _ _
    have h1 : |t| ^ 3 ≤ |t| ^ 3 + 1 := by linarith
    calc ε * |t| ^ 3 ≤ (δ / (2 * (|t| ^ 3 + 1))) * |t| ^ 3 := by gcongr
      _ ≤ (δ / (2 * (|t| ^ 3 + 1))) * (|t| ^ 3 + 1) := by gcongr
      _ = δ / 2 := by field_simp
  have hLind_ε := hLind ε hε_pos
  rw [Metric.tendsto_nhds] at hLind_ε
  have hLind_small : ∀ᶠ n in atTop,
      |(1 / momentSumTriangular X P n) * ∑ k : Fin n,
        ∫ ω in LindebergSetTriangular X P k ε, (X n k ω) ^ 2 ∂P|  < δ / (2 * t ^ 2) := by
    have := hLind_ε (δ / (2 * t ^ 2)) (div_pos hδ (by linarith [sq_pos_of_ne_zero ht]))
    simpa [abs_div, Real.dist_eq, sub_zero] using this
  filter_upwards [hLind_small, hmSum_pos] with n hsmall hpos
  have hX2_int : ∀ n k, Integrable (fun ω => (X n k ω) ^ 2) P :=
    fun n k => (hX_MemL2 n k).integrable_sq
  set s := √(momentSumTriangular X P n) with hs_def
  have hs_sq : s ^ 2 = momentSumTriangular X P n := by rw [hs_def, Real.sq_sqrt (by positivity)]
  simp only [← hs_sq, Pi.pow_apply, Complex.ofReal_pow,
    dist_zero_right, gt_iff_lt]
  set u : ℝ := t / s with hu_def
  -- Define the integrand: `gₖ = exp(iuX_{n,k}) - 1 - iuX_{n,k} + (uX_{n,k})²/2`.
  let g : Fin n → Ω → ℂ := fun k ω =>
    cexp ((u * X n k ω) * I) - 1 - (u * X n k ω) * I + ((u * X n k ω) ^ 2 / 2)
  -- Global quadratic and cubic bounds on the integrand.
  have hg_bound_quad : ∀ k ω, ‖g k ω‖ ≤ (u * X n k ω) ^ 2 := by
    intro k ω
    simp only [g]
    exact_mod_cast norm_cexp_mul_I_bound_sub_taylor_2_quadratic (u * X n k ω)
  have hg_bound_cubic : ∀ k ω, ‖g k ω‖ ≤ |u * X n k ω| ^ 3 / 6 := by
    intro k ω
    dsimp [g]; exact_mod_cast norm_cexp_mul_I_bound_sub_taylor_2_cubic (u * X n k ω)
  -- Integrability of `g` and `‖g‖`, from the shared remainder lemma.
  have hg_int : ∀ k, Integrable (fun ω => (g k ω)) P := by
    intro k
    simp only [g]
    exact_mod_cast integrable_cexp_remainder_two (hX_meas n k) (hX_MemL2 n k) u
  have hg_norm_int : ∀ k, Integrable (fun ω => ‖g k ω‖) P := fun k => (hg_int k).norm
  -- `φ_{X_{n,k}}(t/sₙ) - 1 + σ_{n,k}² * t²/(2sₙ²) = ∫ gₖ`, by the shared remainder identity.
  have hsummand : ∀ k,
      charFun (P.map (X n k)) u - 1 + P[(X n k) ^ 2] * t ^ 2 / (2 * s ^ 2) = ∫ ω, g k ω ∂P := by
    intro k
    have h := charFun_sub_one_add_eq_integral_remainder (hX_meas n k) (hX_centred n k)
      (hX_MemL2 n k) u
    have hs_pos : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.mpr hpos
    have hco : u ^ 2 * P[(X n k) ^ 2] / 2 = P[(X n k) ^ 2] * t ^ 2 / (2 * s ^ 2) := by
      rw [hu_def]; field_simp [hs_pos.ne']
    rw [hco] at h
    simp only [g]
    exact_mod_cast h
  -- Rewrite the goal's sum in terms of integrals.
  have hrewrite : ∑ k : Fin n,
      (charFun (P.map (X n k)) u - 1 + (P[(X n k) ^ 2] * t ^ 2 / (2 * s ^ 2))) =
      ∑ k : Fin n, ∫ ω, g k ω ∂P :=
    Finset.sum_congr rfl fun k _ => hsummand k
  simp only [Pi.pow_apply, Complex.ofReal_pow] at hrewrite
  rw [hrewrite]
  -- Bound the norm of the sum.
  have hnorm_sum : ‖∑ k : Fin n, ∫ ω, g k ω ∂P‖ ≤ ∑ k : Fin n, ‖∫ ω, g k ω ∂P‖ := norm_sum_le _ _
  -- Norm bounds for the integral of `gₖ` over `Aₖ` and `Aₖᶜ` for each `k`.
  set A : Fin n → Set Ω := fun k => LindebergSetTriangular X P k ε with hA_def
  have hA : ∀ k, MeasurableSet (A k) := fun k =>
    measurableSet_lt measurable_const (hX_meas n k).abs
  have hA_bound : ∀ k : Fin n,
      ∫ ω in A k, ‖g k ω‖ ∂P
        ≤ (t ^ 2 / s ^ 2) * ∫ ω in A k, (X n k ω) ^ 2 ∂P := by
    intro k
    have hpt : ∀ ω ∈ A k, ‖g k ω‖ ≤ (t ^ 2 / s ^ 2) * (X n k ω) ^ 2 := by
      intro ω _
      have hcoef : (u * X n k ω) ^ 2 = (t ^ 2 / s ^ 2) * (X n k ω) ^ 2 := by
        have h : (u * X n k ω) ^ 2 = u ^ 2 * (X n k ω) ^ 2 := by ring
        rw [hu_def]; field_simp
      rw [← hcoef]; exact (hg_bound_quad k ω)
    have hcoef_nn : 0 ≤ t ^ 2 / s ^ 2 := by positivity
    calc
      ∫ ω in A k, ‖g k ω‖ ∂P
          ≤ ∫ ω in A k, (t ^ 2 / s ^ 2) * (X n k ω) ^ 2 ∂P := by
        refine setIntegral_mono_on (hg_norm_int k).integrableOn
          (((hX2_int n k).const_mul (t ^ 2 / s ^ 2)).integrableOn) (hA k) hpt
      _ = (t ^ 2 / s ^ 2) * ∫ ω in A k, (X n k ω) ^ 2 ∂P := integral_const_mul _ _
  have hAc_bound : ∀ k : Fin n, ∫ ω in (A k)ᶜ, ‖g k ω‖ ∂P ≤ ε * |t| * u ^ 2 * P[(X n k) ^ 2] := by
    intro k
    have hpt : ∀ ω ∈ (A k)ᶜ, ‖g k ω‖ ≤ ε * |t| * (u * X n k ω) ^ 2 := by
      intro ω hω
      simp only [A, Set.mem_compl_iff, LindebergSetTriangular, Set.mem_ofPred_eq, not_lt] at hω
      have habs : |u * X n k ω| ≤ ε * |t| := by
        rw [abs_mul, hu_def, abs_div, abs_of_pos (by positivity : 0 < s)]
        calc |t| / s * |X n k ω| ≤ |t| / s * (ε * s) := by gcongr
        _ = ε * |t| := by field_simp; exact div_self (ne_of_gt (by positivity : 0 < s))
      calc ‖g k ω‖ ≤ |u * X n k ω| ^ 3 / 6 := hg_bound_cubic k ω
      _≤ |u * X n k ω| ^ 3 := by exact div_le_self (by positivity) (by norm_num)
      _= |u * X n k ω| * |u * X n k ω| ^ 2 := by ring
      _= |u * X n k ω| * (u * X n k ω) ^ 2 := by rw [sq_abs _]
      _≤ ε * |t| * (u * X n k ω) ^ 2 := by apply mul_le_mul_of_nonneg_right habs (sq_nonneg _)
    have hbd : Integrable (fun ω => ε * |t| * u ^ 2 * (X n k ω) ^ 2) P := (hX2_int n k).const_mul _
    calc ∫ ω in (A k)ᶜ, ‖g k ω‖ ∂P
      ≤ ∫ ω in (A k)ᶜ, ε * |t| * (u * X n k ω) ^ 2 ∂P :=
        setIntegral_mono_on (hg_int k).norm.integrableOn
          (by simpa only [mul_pow, ← mul_assoc] using hbd.integrableOn) (hA k).compl hpt
    _ ≤ ∫ ω, ε * |t| * (u * X n k ω) ^ 2 ∂P :=
        setIntegral_le_integral (by simpa only [mul_pow, ← mul_assoc] using hbd)
          (ae_of_all _ fun ω => by positivity)
    _ = ε * |t| * u ^ 2 * P[(X n k) ^ 2] := by
      rw [show (fun ω => ε * |t| * (u * X n k ω) ^ 2) =
          fun ω => (ε * |t| * u ^ 2) * (X n k ω) ^ 2 from
        funext fun ω => by ring, integral_const_mul]
      simp
  -- Bound each `‖∫ gₖ‖` via splitting the integral.
  have heach_bd : ∀ k, ‖∫ ω, g k ω ∂P‖ ≤ (t ^ 2 / s ^ 2) * ∫ ω in A k, (X n k ω) ^ 2 ∂P
    + ε * |t| * u ^ 2 * P[(X n k) ^ 2] := by
    intro k
    calc ‖∫ ω, g k ω ∂P‖ ≤ ∫ ω, ‖g k ω‖ ∂P := norm_integral_le_integral_norm _
    _ = ∫ ω in A k, ‖g k ω‖ ∂P + ∫ ω in (A k)ᶜ, ‖g k ω‖ ∂P :=
      (integral_add_compl (hA k) (hg_norm_int k)).symm
    _ ≤ (t ^ 2 / s ^ 2) * ∫ ω in A k, (X n k ω) ^ 2 ∂P +
        ε * |t| * u ^ 2 * P[(X n k) ^ 2] := by
      exact add_le_add (hA_bound k) (hAc_bound k)
  -- Sum over all `k`.
  have hsum_bd : ∑ k, ‖∫ ω, g k ω ∂P‖ ≤
    (t ^ 2 / s ^ 2) * ∑ k, ∫ ω in A k, (X n k ω) ^ 2 ∂P + ε * |t| * u ^ 2 * s ^ 2 := by
    calc ∑ k, ‖∫ ω, g k ω ∂P‖
     ≤ ∑ k, ((t ^ 2 / s ^ 2) * ∫ ω in A k, (X n k ω) ^ 2 ∂P +
        (ε * |t| * u ^ 2 * P[(X n k) ^ 2])) := Finset.sum_le_sum fun k _ => heach_bd k
    _= ∑ k, (t ^ 2 / s ^ 2) * ∫ ω in A k, (X n k ω) ^ 2 ∂P +
        ∑ k, ε * |t| * u ^ 2 * P[(X n k) ^ 2] := Finset.sum_add_distrib
    _= (t ^ 2 / s ^ 2) * ∑ k, ∫ ω in A k, (X n k ω) ^ 2 ∂P +
        ε * |t| * u ^ 2 * s ^ 2 := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, hs_sq]
  -- First term `< δ/2`.
  have hfirst : (t ^ 2 / s ^ 2) * ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P < δ / 2 := by
    have hsum_nonneg : 0 ≤ ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P :=
      Finset.sum_nonneg fun k _ => integral_nonneg fun _ => sq_nonneg _
    have hLind_bd : (1 / s ^ 2) * ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P < δ / (2 * t ^ 2) := by
      rw [←hs_sq, abs_of_nonneg (mul_nonneg (by positivity) (hsum_nonneg))] at hsmall
      exact hsmall
    have htpos : 0 < t ^ 2 := by positivity
    calc
      (t ^ 2 / s ^ 2) * ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P =
          t ^ 2 * (1 / s ^ 2 * ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P) := by
        rw [div_eq_mul_inv]
        ring
      _ < t ^ 2 * (δ / (2 * t ^ 2)) := by
        exact mul_lt_mul_of_pos_left hLind_bd htpos
      _ = δ / 2 := by field_simp
  -- Second term = `ε · |t|³`.
  have hsecond : ε * |t| * u ^ 2 * s ^ 2 = ε * |t| ^ 3 := by
    rw [hu_def]
    field_simp
    rw [←sq_abs t]
    field_simp [ne_of_gt hpos]
    exact mul_inv_cancel₀ (by positivity)
  linarith

/-- Under the Lindeberg condition, `∑ₖ (φ_{X_{n,k}}(t/sₙ) - 1) → -t²/2` -/
private lemma tendsto_sum_charFun_sub {X : (n : ℕ) → Fin n → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hX_meas : ∀ n k, Measurable (X n k))
    (hX_centred : ∀ n k, P[X n k] = 0)
    (hX_MemL2 : ∀ n k, MemLp (X n k) 2 P)
    (hLind : LindebergConditionTriangular X P)
    (hmSum_pos : ∀ᶠ n in atTop, 0 < momentSumTriangular X P n)
    (t : ℝ) :
    Tendsto (fun n ↦ ∑ k : Fin n,
      (charFun (P.map (X n k)) (t / √(momentSumTriangular X P n)) - 1)) atTop
      (𝓝 (-(t ^ 2 / 2))) := by
    -- Begin by splitting the sum, `∑ₖ (φ_{X_{n,k}}(t/sₙ) - 1) =`
  -- `∑ₖ (φ_{X_{n,k}}(t/sₙ) - 1 + σ_{n,k}² * t² /(2sₙ²)) - ∑ₖ σ_{n,k}² * t² /(2sₙ²)`.
  have hsplit : (fun n ↦ ∑ k : Fin n,
        (charFun (P.map (X n k)) (t / √(momentSumTriangular X P n)) - 1))
      = fun n ↦ (∑ k : Fin n,
          (charFun (P.map (X n k)) (t / √(momentSumTriangular X P n)) - 1
            + (P[(X n k) ^ 2] * t ^ 2 / (2 * momentSumTriangular X P n))))
        - ∑ k : Fin n, (P[(X n k) ^ 2] * t ^ 2 / (2 * momentSumTriangular X P n) : ℂ) := by
    funext n
    rw [Finset.sum_add_distrib, add_sub_cancel_right]
  rw [hsplit]
  -- hsummand_one: the bracketed sum vanishes as `n → ∞`.
  have hsummand_one := tendsto_sum_charFun_sub_add hX_meas hX_centred hX_MemL2 hLind hmSum_pos t
  -- hsummand_two: once `sₙ² > 0` the correction sum converges to `t²/2` (in fact, it is
  --exactly `t²/2`) as `n → ∞`.
  have hsummand_two : Tendsto (fun n ↦ ∑ k : Fin n,
        (P[(X n k) ^ 2] * t ^ 2 / (2 * momentSumTriangular X P n) : ℂ)) atTop
        (𝓝 ((t ^ 2 / 2 : ℝ) : ℂ)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hmSum_pos] with n hn
    have hsne : momentSumTriangular X P n ≠ 0 := ne_of_gt hn
    symm
    rw [← (show ∑ k : Fin n, P[(X n k) ^ 2] * t ^ 2 / (2 * momentSumTriangular X P n) = t ^ 2 / 2
        from by
      rw [← Finset.sum_div, ← Finset.sum_mul]; field_simp)]
    push_cast [integral_complex_ofReal]
    rfl
  -- Combine to give the final result.
  have hcomb := hsummand_one.sub hsummand_two
  push_cast at hcomb ⊢
  rwa [zero_sub] at hcomb

/-- If Feller negligibility holds then `∑ₖ |φ_{X_{n,k}}(t/sₙ) - 1|² → 0`. -/
private lemma tendsto_sum_abs_charFun_sub_one_sq_of_Feller {X : (n : ℕ) → Fin n → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hX_meas : ∀ n k, Measurable (X n k))
    (hX_centred : ∀ n k, P[X n k] = 0)
    (hX_MemL2 : ∀ n k, MemLp (X n k) 2 P)
    (hmSum_pos : ∀ᶠ n in atTop, 0 < momentSumTriangular X P n)
    (hFeller : Tendsto (fun n ↦ (⨆ k : Fin n, P[(X n k) ^ 2]) / momentSumTriangular X P n)
      atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n ↦ ∑ k : Fin n,
      ‖charFun (P.map (X n k)) (t / √ (momentSumTriangular X P n)) - 1‖ ^ 2) atTop (𝓝 0) := by
  -- Apply Feller negligibility
  rw [Metric.tendsto_nhds]
  intro δ hδ
  rw [Metric.tendsto_nhds] at hFeller
  filter_upwards [hFeller (δ / (t ^ 4 / 4 + 1)) (by positivity), hmSum_pos] with n hFeller_n hpos
  set s := √(momentSumTriangular X P n) with hs_def
  have hs_sq : s ^ 2 = momentSumTriangular X P n := by rw [hs_def, Real.sq_sqrt (by positivity)]
  set u : ℝ := t / s with hu_def
  -- Bound `‖φ_{X_{n,k}(u) - 1‖ ≤ u² σ_{n,k}² / 2`. Since `E[X_{n,k}] = 0`, we have
  -- `φ_{X_{n,k}}(u) - 1 = E[exp(iuX_{n,k}) - 1 - iuX_{n,k}]`, and `‖exp(iy) - 1 - iy‖ ≤ y²/2`.
  have heach_bound : ∀ k : Fin n,
      ‖charFun (P.map (X n k)) u - 1‖ ≤ u ^ 2 / 2 * P[(X n k) ^ 2] := by
    intro k
    -- Taylor-1 bound: `‖exp(iy) - 1 - iy‖ ≤ y²/2`.
    have hpt : ∀ y : ℝ, ‖cexp (↑y * I) - 1 - ↑y * I‖ ≤ y ^ 2 / 2 := fun y => by
      rw [← sq_abs]; exact norm_cexp_mul_I_sub_taylor_1 y
    -- Define `f = exp(iuX_{n,k}) - 1 - iuX_{n,k}`, with `‖f‖ ≤ (uX_{n,k})²/2`.
    set f : Ω → ℂ := fun ω => cexp (↑(u * X n k ω) * I) - 1 - ↑(u * X n k ω) * I with hf_def
    have hf_bound : ∀ ω, ‖f ω‖ ≤ (u * X n k ω) ^ 2 / 2 := fun ω => hpt (u * X n k ω)
    have hbd_int : Integrable (fun ω => (u * X n k ω) ^ 2 / 2) P :=
      ((hX_MemL2 n k).integrable_sq.const_mul (u ^ 2 / 2)).congr
        (ae_of_all _ fun ω => by ring)
    -- `φ_{X_{n,k}}(u) - 1 = ∫ f`, by the shared remainder identity.
    have hint_eq : charFun (P.map (X n k)) u - 1 = ∫ ω, f ω ∂P :=
      charFun_sub_one_eq_integral_remainder (hX_meas n k) (hX_centred n k)
        ((hX_MemL2 n k).integrable one_le_two) u
    rw [hint_eq]
    calc ‖∫ ω, f ω ∂P‖
        ≤ ∫ ω, ‖f ω‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (u * X n k ω) ^ 2 / 2 ∂P := by
          refine integral_mono_of_nonneg (ae_of_all _ fun ω => norm_nonneg _) hbd_int ?_
          exact ae_of_all _ hf_bound
      _ = u ^ 2 / 2 * P[(X n k) ^ 2] := by
          have heq : (fun ω => (u * X n k ω) ^ 2 / 2) = (fun ω => (u ^ 2 / 2) * X n k ω ^ 2) := by
            ext ω; ring
          rw [heq, integral_const_mul]; simp
  have hvar_nn : ∀ k : Fin n, 0 ≤ P[(X n k) ^ 2] := fun k =>
    integral_nonneg fun _ => sq_nonneg _
  set M := ⨆ k : Fin n, P[(X n k) ^ 2] with hM_def
  have hM_nn : 0 ≤ M := by
    by_cases hn : n = 0
    · subst hn; simp [M]
    · have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨0, Nat.pos_of_ne_zero hn⟩
        (hvar_nn ⟨0, Nat.pos_of_ne_zero hn⟩)
  have hM_le : ∀ k : Fin n, P[(X n k) ^ 2] ≤ M := by
    intro k
    have hne : Nonempty (Fin n) := ⟨k⟩
    exact le_ciSup (f := fun k : Fin n => P[(X n k) ^ 2])
      (Finite.bddAbove_range _) k
  -- Bound each `‖φ_{X_{n,k}}(u) - 1‖²` and then sum
  have h_each_sq : ∀ k : Fin n,
      ‖charFun (P.map (X n k)) u - 1‖ ^ 2 ≤ u ^ 4 / 4 * (M * P[(X n k) ^ 2]) := by
    intro k
    have h := heach_bound k
    have hnn : 0 ≤ ‖charFun (P.map (X n k)) u - 1‖ := norm_nonneg _
    have hsq : ‖charFun (P.map (X n k)) u - 1‖ ^ 2 ≤ (u ^ 2 / 2 * P[(X n k) ^ 2]) ^ 2 :=
      pow_le_pow_left₀ hnn h 2
    have hexp : (u ^ 2 / 2 * P[(X n k) ^ 2]) ^ 2 =
        u ^ 4 / 4 * (P[(X n k) ^ 2] * P[(X n k) ^ 2]) := by ring
    rw [hexp] at hsq
    have h_uv_nn : 0 ≤ u ^ 4 / 4 := by positivity
    have : P[(X n k) ^ 2] * P[(X n k) ^ 2] ≤ M * P[(X n k) ^ 2] :=
      mul_le_mul_of_nonneg_right (hM_le k) (hvar_nn k)
    linarith [mul_le_mul_of_nonneg_left this h_uv_nn]
  have hsum_le :
      ∑ k : Fin n, ‖charFun (P.map (X n k)) u - 1‖ ^ 2 ≤ t ^ 4 / 4 * (M / s ^ 2) := by
    calc ∑ k : Fin n, ‖charFun (P.map (X n k)) u - 1‖ ^ 2
        ≤ ∑ k : Fin n, u ^ 4 / 4 * (M * P[(X n k) ^ 2]) :=
          Finset.sum_le_sum fun k _ => h_each_sq k
      _ = u ^ 4 / 4 * M * momentSumTriangular X P n := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = u ^ 4 / 4 * M * (s ^ 2) := by rw [hs_sq]
      _ = t ^ 4 / 4 * (M / s ^ 2) := by rw [hu_def]; field_simp
  -- Show that `M/s < δ/(t⁴/4+1)`
  have hMs_nn : 0 ≤ M / s ^ 2 := div_nonneg hM_nn (by positivity)
  have hFeller_n' : M / s ^ 2 < δ / (t ^ 4 / 4 + 1) := by
    rw [Real.dist_eq, sub_zero, ← hs_sq, abs_of_nonneg hMs_nn] at hFeller_n
    exact hFeller_n
  -- Conclude
  rw [Real.dist_eq, sub_zero]
  have h_sum_nn : 0 ≤ ∑ k : Fin n, ‖charFun (P.map (X n k)) u - 1‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [abs_of_nonneg h_sum_nn]
  have hbd : t ^ 4 / 4 * (M / s ^ 2) < δ := by
    calc t ^ 4 / 4 * (M / s ^ 2)
       ≤ (t ^ 4 / 4 + 1) * (M / s ^ 2) := by
          linarith [hMs_nn]
      _< (t ^ 4 / 4 + 1) * (δ / (t ^ 4 / 4 + 1)) := by
          have ht4_pos : 0 < (δ / (t ^ 4 / 4 + 1)) := by positivity
          exact mul_lt_mul_of_pos_left (hFeller_n') (by positivity)
      _= δ := by field_simp
  linarith

end IntermediateResults


section TriangularArrayResults

/-- The Lindeberg condition implies Feller negligibility: `maxₖ σ_{n,k}² / sₙ² → 0`. -/
lemma Feller_negligibility_of_Lindeberg_Triangular {X : (n : ℕ) → Fin n → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hX_meas : ∀ n k, Measurable (X n k))
    (hX_MemL2 : ∀ n k, MemLp (X n k) 2 P)
    (hLind : LindebergConditionTriangular X P)
    (hmSum_pos : ∀ᶠ n in atTop, 0 < momentSumTriangular X P n) :
    Tendsto (fun n ↦ (⨆ k : Fin n, P[(X n k) ^ 2]) / momentSumTriangular X P n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hε : (0 : ℝ) < Real.sqrt (δ / 2) := Real.sqrt_pos.mpr (by positivity)
  set ε := Real.sqrt (δ / 2)
  have hLind_ε := hLind ε hε
  rw [Metric.tendsto_nhds] at hLind_ε
  have hev := hLind_ε (δ / 2) (by positivity)
  simp only [Real.dist_eq, sub_zero] at hev
  filter_upwards [hev, hmSum_pos] with n hsmall hpos
  have hX2_int : ∀ n k, Integrable (fun ω => (X n k ω) ^ 2) P :=
    fun n k => (hX_MemL2 n k).integrable_sq
  have hiSup_nonneg : 0 ≤ ⨆ k : Fin n, P[(X n k) ^ 2] := by
    by_cases hn : n = 0
    · subst hn; simp
    · have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨0, Nat.pos_of_ne_zero hn⟩
        (integral_nonneg fun ω ↦ sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hiSup_nonneg hpos.le)]
  set s := √(momentSumTriangular X P n) with hs_def
  have hs_sq : s ^ 2 = momentSumTriangular X P n := by rw [hs_def, Real.sq_sqrt (by positivity)]
  simp only [← hs_sq, Pi.pow_apply, gt_iff_lt]
  set A : Fin n → Set Ω := fun k => LindebergSetTriangular X P k ε with hA_def
  have hA : ∀ k, MeasurableSet (A k) := fun k =>
    measurableSet_lt measurable_const (hX_meas n k).abs
  have htrunc_nonneg : ∀ k, 0 ≤ ∫ ω in A k, (X n k ω) ^ 2 ∂P := fun k =>
    integral_nonneg fun _ => sq_nonneg _
  -- Show that each `E[X_{n,k}²] ≤ (εsₙ)² + ∫_{Aₖ} X_{n,k}²`.
  have hbound : ∀ k : Fin n,
      P[(X n k) ^ 2] ≤ (ε * s) ^ 2 + ∫ ω in A k, (X n k ω) ^ 2 ∂P := by
    intro k
    have h_bdd_on : ∀ ω ∈ (A k)ᶜ, (X n k ω) ^ 2 ≤ (ε * s) ^ 2 := by
      intro ω hω
      simp only [A, LindebergSetTriangular, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω
      rw [← hs_def] at hω
      calc X n k ω ^ 2 = |X n k ω| ^ 2 := (sq_abs _).symm
      _≤ (ε * s) ^ 2 := by gcongr
    have h_int_compl : ∫ ω in (A k)ᶜ, (X n k ω) ^ 2 ∂P ≤ (ε * s) ^ 2 := by
      have h_le_one : (P ((A k)ᶜ)).toReal ≤ 1 := by
        have h := prob_le_one (μ := P) (s := (A k)ᶜ)
        have := ENNReal.toReal_mono (a := P ((A k)ᶜ)) (b := 1) (by simp) h
        simpa using this
      calc ∫ ω in (A k)ᶜ, (X n k ω) ^ 2 ∂P
        ≤ ∫ _ in (A k)ᶜ, (ε * s) ^ 2 ∂P := by
            refine setIntegral_mono_on (hX2_int n k).integrableOn ?_ (hA k).compl h_bdd_on
            exact (integrable_const _).integrableOn
        _= P.real ((A k)ᶜ) * (ε * s) ^ 2 := by
            rw [setIntegral_const, smul_eq_mul]
        _≤ 1 * (ε * s) ^ 2 := by
            have hpr : P.real ((A k)ᶜ) ≤ 1 := by
              simpa [Measure.real] using h_le_one
            gcongr
        _= (ε * s) ^ 2 := one_mul _
    have hsum := integral_add_compl (hA k) (hX2_int n k)
    have hvar_eq : P[(X n k) ^ 2] =
         ∫ ω in A k, (X n k ω) ^ 2 ∂P + ∫ ω in (A k)ᶜ, (X n k ω) ^ 2 ∂P := hsum.symm
    linarith
  -- Deduce that each `E[X_{n,k}²] ≤ (εsₙ)² + Σₖ ∫_{Aₖ} X_{n,k}²`, allowing us to apply
  --the Lindeberg condition after dividing through by `sₙ²`.
  have hsum_nonneg : 0 ≤ ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P :=
    Finset.sum_nonneg fun k _ => htrunc_nonneg k
  have hiSup_le : (⨆ k : Fin n, P[(X n k) ^ 2]) ≤
      (ε * s) ^ 2 + ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P := by
    by_cases hn : n = 0
    · subst hn
      have h0 : (⨆ k : Fin 0, P[(X 0 k) ^ 2]) = 0 := by simp
      rw [h0]
      have : (0 : ℝ) ≤ (ε * s) ^ 2 := by positivity
      linarith [hsum_nonneg]
    · have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      apply ciSup_le
      intro k
      calc P[(X n k) ^ 2]
          ≤ (ε * s) ^ 2 + ∫ ω in A k, (X n k ω) ^ 2 ∂P := hbound k
        _ ≤ (ε * s) ^ 2 + ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P := by
            gcongr
            exact Finset.single_le_sum
              (f := fun k => ∫ ω in A k, (X n k ω) ^ 2 ∂P)
              (fun i _ => htrunc_nonneg i) (Finset.mem_univ k)
  have hsmall' : (1  / s ^ 2) * ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P < δ / 2 := by
    have hnn : 0 ≤ (1  / s ^ 2) * ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P :=
      mul_nonneg (by positivity) (by positivity)
    rwa [← hs_sq, abs_of_nonneg hnn] at hsmall
  have hε_sq : ε ^ 2 = δ / 2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ δ / 2)
  calc (⨆ k : Fin n, P[(X n k) ^ 2]) / s ^ 2
     ≤ ((ε * s) ^ 2 + ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P) / s ^ 2 := by gcongr
    _= ε ^ 2 + (1  / s ^ 2) * ∑ k : Fin n, ∫ ω in A k, (X n k ω) ^ 2 ∂P := by field
    _< δ / 2 + δ / 2 := by rw [hε_sq]; linarith
    _= δ := by ring

/-- The Lindeberg CLT for triangular arrays (characteristic function version). -/
theorem central_limit_charFun_Lindeberg_Triangular {X : (n : ℕ) → Fin n → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hX_meas : ∀ n k, Measurable (X n k))
    (hX_ind : ∀ n, iIndepFun (X n) P)
    (hX_centred : ∀ n k, P[X n k] = 0)
    (hX_MemL2 : ∀ n k, MemLp (X n k) 2 P)
    (hLind : LindebergConditionTriangular X P)
    (hmSum_pos : ∀ᶠ n in atTop, 0 < momentSumTriangular X P n)
    (t : ℝ) :
    Tendsto (fun n ↦ charFun (P.map (LindebergSumTriangular X P n)) t) atTop
      (𝓝 (cexp (-(t ^ 2 / 2)))) := by
  have hFeller := Feller_negligibility_of_Lindeberg_Triangular hX_meas hX_MemL2 hLind hmSum_pos
  simp_rw [charFun_LindebergSumTriangular hX_meas hX_ind]
  have hprod : ∀ n, ∏ k : Fin n,
      charFun (P.map (X n k)) (t / √(momentSumTriangular X P n))  =
      ∏ k : Fin n, (1 + (charFun (P.map (X n k)) (t / √(momentSumTriangular X P n)) - 1)) := by
    intro n; congr 1; ext k; ring
  simp_rw [hprod]
  exact tendsto_finset_prod_one_add_of_sum_of_sq
    (tendsto_sum_charFun_sub hX_meas hX_centred hX_MemL2 hLind hmSum_pos t)
    (tendsto_sum_abs_charFun_sub_one_sq_of_Feller hX_meas hX_centred hX_MemL2 hmSum_pos hFeller t)

/-- The Lindeberg CLT for triangular arrays (convergence in distribution version). -/
theorem central_limit_Lindeberg_Triangular {X : (n : ℕ) → Fin n → Ω → ℝ}
    {P : ProbabilityMeasure Ω}
    (hX_meas : ∀ n k, Measurable (X n k))
    (hX_ind : ∀ n, iIndepFun (X n) P)
    (hX_centred : ∀ n k, P[X n k] = 0)
    (hX_MemL2 : ∀ n k, MemLp (X n k) 2 P)
    (hLind : LindebergConditionTriangular X P)
    (hmSum_pos : ∀ᶠ n in atTop, 0 < momentSumTriangular X P n) :
    Tendsto (fun n : ℕ ↦ P.map (aemeasurable_LindebergSumTriangular n hX_meas)) atTop
      (𝓝 stdGaussian) := by
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr fun t ↦ ?_
  have hgauss : charFun ((stdGaussian : ProbabilityMeasure ℝ) : Measure ℝ) t
      = cexp (-(t ^ 2 / 2)) := by
    change charFun (gaussianReal 0 1) t = _
    rw [charFun_gaussianReal]; push_cast; ring_nf
  rw [hgauss]
  simp only [ProbabilityMeasure.toMeasure_map]
  exact central_limit_charFun_Lindeberg_Triangular hX_meas hX_ind hX_centred hX_MemL2
    hLind hmSum_pos t

end TriangularArrayResults


section SequenceDefinitions

/-- The sum of moments `sₙ² = ∑ₖ σₖ²` (assuming random variables `Xₖ` are mean-zero) -/
abbrev momentSum (X : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ) : ℝ := ∑ (k : Fin n), P[(X k) ^ 2]

/-- The domain of integration `{|Xₖ| > εsₙ}` appearing in the Lindeberg condition -/
def LindebergSet (X : ℕ → Ω → ℝ) (P : Measure Ω) {n : ℕ} (k : Fin n) (ε : ℝ) : Set Ω :=
  {ω | ε * (Real.sqrt (momentSum X P n)) < |X k ω|}

/-- The Lindeberg condition (sequence): for all `ε > 0`,
`(1/sₙ²) ∑ₖ ∫_{|Xₖ| > εsₙ} Xₖ² dP → 0`. -/
def LindebergCondition (X : ℕ → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ ε > (0 : ℝ), Tendsto (fun n ↦
    (1 / momentSum X P n) * ∑ k : Fin n, ∫ ω in (LindebergSet X P k ε), (X k ω) ^ 2 ∂P)
    atTop (𝓝 0)

/-- The normalized partial sum: `Sₙ/sₙ = (Σₖ Xₖ)/sₙ`. -/
abbrev LindebergSum (X : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ) (ω : Ω) : ℝ :=
   (∑ k : Fin n, X k ω) / (√(momentSum X P n))

/-- `Sₙ/sₙ` is a.e.-measurable — needed to form its pushforward probability measure. -/
lemma aemeasurable_LindebergSum {X : ℕ → Ω → ℝ} {μ : Measure Ω} (n : ℕ)
    (hX_meas : ∀ k, Measurable (X k)) :
    AEMeasurable (LindebergSum X μ n) μ := by fun_prop

/-- Global independence of the sequence restricts to row-wise independence of any
finite initial segment `{Xₖ}_{k : Fin n}`. -/
lemma iIndepFun_fin_of_iIndepFun {X : ℕ → Ω → ℝ} {P : Measure Ω}
    (hX_ind : iIndepFun X P) (n : ℕ) :
    iIndepFun (fun k : Fin n ↦ X k) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S s hs
  convert hX_ind.measure_inter_preimage_eq_mul (S.map Fin.valEmbedding)
    (sets := fun k ↦ if h : k < n then s ⟨k, h⟩ else ∅) ?_
  · simp
  · simp
  · simpa

end SequenceDefinitions

section SequenceResults

/-- The Lindeberg condition implies Feller negligibility: `maxₖ σₖ² / sₙ² → 0`. -/
lemma Feller_negligibility_of_Lindeberg
    {X : ℕ → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hX_meas : ∀ k, Measurable (X k))
    (hX_MemL2 : ∀ k, MemLp (X k) 2 P)
    (hLind : LindebergCondition X P)
    (hmSum_pos : ∀ᶠ n in atTop, 0 < momentSum X P n) :
    Tendsto (fun n ↦ (⨆ k : Fin n, P[(X k) ^ 2]) / momentSum X P n) atTop (𝓝 0) :=
  Feller_negligibility_of_Lindeberg_Triangular (X := fun n (k : Fin n) ↦ X k)
    (fun _ k ↦ hX_meas k) (fun _ k ↦ hX_MemL2 k) hLind hmSum_pos

/-- The Lindeberg CLT (characteristic function version). -/
theorem central_limit_charFun_Lindeberg
    {X : ℕ → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hX_meas : ∀ k, Measurable (X k))
    (hX_ind : iIndepFun X P)
    (hX_centred : ∀ k, P[X k] = 0)
    (hX_MemL2 : ∀ k, MemLp (X k) 2 P)
    (hLind : LindebergCondition X P)
    (hmSum_pos : ∀ᶠ n in atTop, 0 < momentSum X P n)
    (t : ℝ) :
    Tendsto (fun n ↦ charFun (P.map (LindebergSum X P n)) t) atTop
      (𝓝 (cexp (-(t ^ 2 / 2)))) :=
  central_limit_charFun_Lindeberg_Triangular (X := fun n (k : Fin n) ↦ X k)
    (fun _ k ↦ hX_meas k) (fun n ↦ iIndepFun_fin_of_iIndepFun hX_ind n)
    (fun _ k ↦ hX_centred k) (fun _ k ↦ hX_MemL2 k)
    hLind hmSum_pos t

/-- The Lindeberg CLT (convergence in distribution version). -/
theorem central_limit_Lindeberg
    {X : ℕ → Ω → ℝ}
    {P : ProbabilityMeasure Ω}
    (hX_meas : ∀ k, Measurable (X k))
    (hX_ind : iIndepFun X P)
    (hX_centred : ∀ k, P[X k] = 0)
    (hX_MemL2 : ∀ k, MemLp (X k) 2 P)
    (hLind : LindebergCondition X P)
    (hmSum_pos : ∀ᶠ n in atTop, 0 < momentSum X P n) :
    Tendsto (fun n : ℕ ↦ P.map (aemeasurable_LindebergSum n hX_meas)) atTop
      (𝓝 stdGaussian) :=
  central_limit_Lindeberg_Triangular (X := fun n (k : Fin n) ↦ X k)
    (fun _ k ↦ hX_meas k) (fun n ↦ iIndepFun_fin_of_iIndepFun hX_ind n) (fun _ k ↦ hX_centred k)
    (fun _ k ↦ hX_MemL2 k) hLind hmSum_pos


end SequenceResults

end
end LinearModel
end LeanPool
