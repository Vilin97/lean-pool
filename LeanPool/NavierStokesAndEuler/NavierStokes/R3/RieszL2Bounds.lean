/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszPairing
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.SchwartzParseval
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactSchwartz
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# The `L²` bound for Riesz operators on Schwartz tests

The Fourier pairing and Schwartz Parseval imply a dual bound. Testing it
against a compact smooth cutoff times the output bounds every truncated
energy. Fatou's lemma then proves both square integrability and the global
bound, without extending the Fourier transform to arbitrary `L²` functions.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff FourierTransform ComplexConjugate ENNReal Topology

namespace NavierStokesR3.RieszTestOperators

open ProblemStatement Comparison

/-- Cauchy--Schwarz and the multiplier bound give the test-function dual estimate. -/
theorem norm_rieszTest_pairing_le (i j : Fin 3) (ψ φ : ComplexTest) :
    ‖∫ x : Space, rieszTest i j ψ x * conj (φ x)‖ ≤
      Real.sqrt (∫ x : Space, ‖ψ x‖ ^ 2) *
        Real.sqrt (∫ x : Space, ‖φ x‖ ^ 2) := by
  let Fψ : ComplexTest := FourierTransform.fourierCLE ℂ ComplexTest ψ
  let Fφ : ComplexTest := FourierTransform.fourierCLE ℂ ComplexTest φ
  have hprod : Integrable (fun ξ : Space => ‖Fψ ξ‖ * ‖Fφ ξ‖) :=
    (Fψ.memLp 2).norm.integrable_mul (Fφ.memLp 2).norm
  rw [rieszTest_pairing_fourier_conj]
  change ‖∫ ξ : Space, (rieszSymbol i j ξ : ℂ) * Fψ ξ * conj (Fφ ξ)‖ ≤ _
  calc
    _ ≤ ∫ ξ : Space, ‖(rieszSymbol i j ξ : ℂ) * Fψ ξ * conj (Fφ ξ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : Space, ‖Fψ ξ‖ * ‖Fφ ξ‖ := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hprod
      filter_upwards [] with ξ
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have hm := mul_le_mul_of_nonneg_right
        (norm_rieszSymbol_complex_le i j ξ) (norm_nonneg (Fψ ξ))
      rw [one_mul] at hm
      exact mul_le_mul_of_nonneg_right hm (norm_nonneg (Fφ ξ))
    _ ≤ _ := by
      have h := integral_mul_norm_le_Lp_mul_Lq
        (μ := (volume : Measure Space)) (f := (Fψ : Space → ℂ))
        (g := (Fφ : Space → ℂ)) Real.HolderConjugate.two_two
        (by simpa using Fψ.memLp 2) (by simpa using Fφ.memLp 2)
      have hψ : (∫ ξ : Space, ‖Fψ ξ‖ ^ 2) = ∫ x : Space, ‖ψ x‖ ^ 2 :=
        SchwartzParseval.integral_norm_sq_fourier ψ
      have hφ : (∫ ξ : Space, ‖Fφ ξ‖ ^ 2) = ∫ x : Space, ‖φ x‖ ^ 2 :=
        SchwartzParseval.integral_norm_sq_fourier φ
      simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, hψ, hφ] using h

private noncomputable def l2Cutoff (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := (n : ℝ) + 1
  rOut := (n : ℝ) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

private theorem l2Cutoff_eventually_one (x : Space) :
    ∀ᶠ n : ℕ in atTop, l2Cutoff n x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply (l2Cutoff n).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ (n : ℝ) + 1
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

private theorem cutoff_energy_le_of_pairing_bound {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ φ : ComplexTest,
      ‖∫ x : Space, f x * conj (φ x)‖ ≤
        Real.sqrt C * Real.sqrt (∫ x : Space, ‖φ x‖ ^ 2))
    (χ : ContDiffBump (0 : Space)) :
    (∫ x : Space, χ x * ‖f x‖ ^ 2) ≤ C := by
  let φ : ComplexTest := CompactSchwartz.ofCompactSupport
    (fun x => χ x • f x) (χ.contDiff.smul hf) χ.hasCompactSupport.smul_right
  have hYi : Integrable (fun x : Space => χ x * ‖f x‖ ^ 2) :=
    (χ.continuous.mul (hf.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      χ.hasCompactSupport.mul_right
  have hY : 0 ≤ ∫ x : Space, χ x * ‖f x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg χ.nonneg (sq_nonneg _)
  have hφY : (∫ x : Space, ‖φ x‖ ^ 2) ≤ ∫ x : Space, χ x * ‖f x‖ ^ 2 := by
    apply integral_mono (SchwartzParseval.integrable_norm_sq φ) hYi
    intro x
    change ‖χ x • f x‖ ^ 2 ≤ χ x * ‖f x‖ ^ 2
    rw [norm_smul, Real.norm_of_nonneg χ.nonneg, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have h0 := χ.nonneg (x := x)
    have h1 := χ.le_one (x := x)
    nlinarith
  have hpair_eq : (∫ x : Space, f x * conj (φ x)) =
      ((∫ x : Space, χ x * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = ∫ x : Space, ((χ x * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        change f x * conj (χ x • f x) = ((χ x * ‖f x‖ ^ 2 : ℝ) : ℂ)
        calc
          _ = (χ x : ℂ) * (f x * conj (f x)) := by
            rw [Algebra.smul_def]
            change f x * conj ((χ x : ℂ) * f x) = _
            rw [map_mul, Complex.conj_ofReal]
            ring
          _ = _ := by simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = _ := by simp only [integral_complex_ofReal]
  have hbound : (∫ x : Space, χ x * ‖f x‖ ^ 2) ≤
      Real.sqrt C * Real.sqrt (∫ x : Space, χ x * ‖f x‖ ^ 2) := by
    have hp := hpair φ
    rw [hpair_eq, Complex.norm_real, Real.norm_of_nonneg hY] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hφY)
      (Real.sqrt_nonneg C))
  nlinarith [sq_nonneg (Real.sqrt C - Real.sqrt (∫ x : Space, χ x * ‖f x‖ ^ 2)),
    Real.sq_sqrt hC, Real.sq_sqrt hY]

/-- A smooth function satisfying the `L²` dual estimate on Schwartz tests is square
integrable with the corresponding bound. -/
theorem memLp_two_and_integral_le_of_pairing_bound {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ φ : ComplexTest,
      ‖∫ x : Space, f x * conj (φ x)‖ ≤
        Real.sqrt C * Real.sqrt (∫ x : Space, ‖φ x‖ ^ 2)) :
    MemLp f 2 volume ∧ (∫ x : Space, ‖f x‖ ^ 2) ≤ C := by
  have hcont (n : ℕ) : Continuous (fun x : Space => l2Cutoff n x * ‖f x‖ ^ 2) :=
    (l2Cutoff n).continuous.mul (hf.continuous.norm.pow 2)
  have hint (n : ℕ) : Integrable (fun x : Space => l2Cutoff n x * ‖f x‖ ^ 2) :=
    (hcont n).integrable_of_hasCompactSupport (l2Cutoff n).hasCompactSupport.mul_right
  have hlin_bound (n : ℕ) :
      (∫⁻ x : Space, ENNReal.ofReal (l2Cutoff n x * ‖f x‖ ^ 2)) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
      (Eventually.of_forall fun x => mul_nonneg (l2Cutoff n).nonneg (sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (cutoff_energy_le_of_pairing_bound hf hC hpair (l2Cutoff n))
  have hlim (x : Space) : Tendsto
      (fun n : ℕ => ENNReal.ofReal (l2Cutoff n x * ‖f x‖ ^ 2))
      atTop (𝓝 (ENNReal.ofReal (‖f x‖ ^ 2))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [l2Cutoff_eventually_one x] with n hn
    simp only [hn, one_mul]
  have hlin : (∫⁻ x : Space, ENNReal.ofReal (‖f x‖ ^ 2)) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x : Space, atTop.liminf
          (fun n : ℕ => ENNReal.ofReal (l2Cutoff n x * ‖f x‖ ^ 2)) := by
        exact lintegral_congr fun x => (hlim x).liminf_eq.symm
      _ ≤ atTop.liminf (fun n : ℕ =>
          ∫⁻ x : Space, ENNReal.ofReal (l2Cutoff n x * ‖f x‖ ^ 2)) :=
        lintegral_liminf_le fun n => (ENNReal.continuous_ofReal.comp (hcont n)).measurable
      _ ≤ ENNReal.ofReal C :=
        liminf_le_of_frequently_le' (Frequently.of_forall hlin_bound)
  have hsq : Integrable (fun x : Space => ‖f x‖ ^ 2) := by
    refine ⟨(hf.continuous.norm.pow 2).aestronglyMeasurable, ?_⟩
    change (∫⁻ x : Space, ‖(‖f x‖ ^ 2 : ℝ)‖ₑ) < (⊤ : ℝ≥0∞)
    simpa only [← ofReal_norm, norm_pow, norm_norm] using
      hlin.trans_lt (ENNReal.ofReal_lt_top : ENNReal.ofReal C < (⊤ : ℝ≥0∞))
  refine ⟨(memLp_two_iff_integrable_sq_norm hf.continuous.aestronglyMeasurable).mpr hsq, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg ‖f x‖)
    hsq.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin).trans_eq (ENNReal.toReal_ofReal hC)

/-- The Riesz test operator is an `L²` contraction, including square integrability. -/
theorem rieszTest_memLp_and_l2_bound (i j : Fin 3) (ψ : ComplexTest) :
    MemLp (rieszTest i j ψ) 2 volume ∧
      (∫ x : Space, ‖rieszTest i j ψ x‖ ^ 2) ≤ ∫ x : Space, ‖ψ x‖ ^ 2 :=
  memLp_two_and_integral_le_of_pairing_bound (contDiff_rieszTest i j ψ)
    (integral_nonneg fun x => sq_nonneg ‖ψ x‖) (norm_rieszTest_pairing_le i j ψ)

theorem memLp_rieszTest (i j : Fin 3) (ψ : ComplexTest) :
    MemLp (rieszTest i j ψ) 2 volume :=
  (rieszTest_memLp_and_l2_bound i j ψ).1

theorem integral_norm_sq_rieszTest_le (i j : Fin 3) (ψ : ComplexTest) :
    (∫ x : Space, ‖rieszTest i j ψ x‖ ^ 2) ≤ ∫ x : Space, ‖ψ x‖ ^ 2 :=
  (rieszTest_memLp_and_l2_bound i j ψ).2

end NavierStokesR3.RieszTestOperators
