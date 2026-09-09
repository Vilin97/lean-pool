/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisCoefficientSpace
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Uniform analytic input for the natural-axis coefficient space

The hypotheses concern one common complex neighborhood of the entire real
parameter interval. Cauchy's integral formula supplies bounds on actual
derivatives; the derivative bounds are not hypotheses of the construction.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.AnalyticCoefficientBounds

open Set Metric Filter Complex
open scoped Topology ContDiff NNReal
open AxisCoefficientSpace

/-- The closed radius-`ρ` neighborhood of the real parameter interval. -/
def closedTube (I : Window) (ρ : ℝ) : Set ℂ :=
  {z | ∃ x ∈ I.interval, dist z (x : ℂ) ≤ ρ}

theorem closedBall_subset_closedTube (I : Window) (ρ : ℝ)
    {x : ℝ} (hx : x ∈ I.interval) :
    closedBall (x : ℂ) ρ ⊆ closedTube I ρ :=
  fun _ hz => ⟨x, hx, hz⟩

theorem real_mem_closedTube (I : Window) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {x : ℝ} (hx : x ∈ I.interval) : (x : ℂ) ∈ closedTube I ρ :=
  ⟨x, hx, by simpa using hρ⟩

/-- A uniform complex value bound, with holomorphy on a neighborhood of
the same closed tube. No derivative estimates occur in this predicate. -/
structure UnitHolomorphic (I : Window) (ρ : ℝ) (f : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ f (closedTube I ρ)
  norm_le_one : ∀ z ∈ closedTube I ρ, ‖f z‖ ≤ 1

/-- Bound one Cauchy coefficient directly by its circle integral. -/
theorem norm_cauchyCoefficient_le {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hb : ∀ z ∈ sphere c ρ, ‖f z‖ ≤ 1) (m : ℕ) :
    ‖cauchyPowerSeries f c ρ m (fun _ => 1)‖ ≤ (ρ⁻¹) ^ m := by
  rw [cauchyPowerSeries_apply]
  have hbound : ∀ z ∈ sphere c ρ,
      ‖(1 / (z - c)) ^ m • (z - c)⁻¹ • f z‖ ≤ (ρ⁻¹) ^ m * ρ⁻¹ := by
    intro z hz
    have hz' : ‖z - c‖ = ρ := by simpa only [mem_sphere, dist_eq_norm] using hz
    rw [norm_smul, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hz', one_div]
    calc
      (ρ⁻¹) ^ m * (ρ⁻¹ * ‖f z‖) ≤ (ρ⁻¹) ^ m * (ρ⁻¹ * 1) := by
        gcongr
        exact hb z hz
      _ = (ρ⁻¹) ^ m * ρ⁻¹ := by ring
  calc
    _ ≤ ρ * ((ρ⁻¹) ^ m * ρ⁻¹) :=
      circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ.le hbound
    _ = (ρ⁻¹) ^ m := by
      calc
        ρ * ((ρ⁻¹) ^ m * ρ⁻¹) = (ρ⁻¹) ^ m * (ρ * ρ⁻¹) := by ring
        _ = (ρ⁻¹) ^ m := by rw [mul_inv_cancel₀ hρ.ne', mul_one]

/-- Cauchy's estimate for every genuine complex derivative, derived from
the circle-integral coefficients and the factorial derivative identity. -/
theorem norm_iteratedDeriv_le {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hf : DifferentiableOn ℂ f (closedBall c ρ))
    (hb : ∀ z ∈ sphere c ρ, ‖f z‖ ≤ 1) (m : ℕ) :
    ‖iteratedDeriv m f c‖ ≤ (m.factorial : ℝ) * (ρ⁻¹) ^ m := by
  let r : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hp := (show DifferentiableOn ℂ f (closedBall c (r : ℝ)) from hf).hasFPowerSeriesOnBall
    (show 0 < r from hρ)
  have heq : iteratedDeriv m f c =
      m.factorial • cauchyPowerSeries f c ρ m (fun _ => 1) := by
    rw [iteratedDeriv_eq_iteratedFDeriv]
    exact (hp.factorial_smul (1 : ℂ) m).symm
  rw [heq, nsmul_eq_mul, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_cauchyCoefficient_le hρ hb m) (by positivity)

/-- The real part of a genuine complex jet, evaluated on the real axis. -/
def realJet (f : ℂ → ℂ) (m : ℕ) (x : ℝ) : ℝ :=
  (iteratedDeriv m f (x : ℂ)).re

theorem hasDerivAt_realJet {f : ℂ → ℂ} {x : ℝ}
    (hf : AnalyticAt ℂ f (x : ℂ)) (m : ℕ) :
    HasDerivAt (realJet f m) (realJet f (m + 1) x) x := by
  have hm : AnalyticAt ℂ (iteratedDeriv m f) (x : ℂ) := by
    simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv m
  unfold realJet
  simpa only [iteratedDeriv_succ] using hm.differentiableAt.hasDerivAt.real_of_complex

/-- The real-axis jets really are the ordinary iterated real derivatives. -/
theorem iteratedDeriv_realPart {f : ℂ → ℂ} {x : ℝ}
    (hf : AnalyticAt ℂ f (x : ℂ)) (m : ℕ) :
    iteratedDeriv m (fun t : ℝ => (f t).re) x = realJet f m x := by
  induction m generalizing x with
  | zero => simp [realJet]
  | succ m ih =>
      have heq : iteratedDeriv m (fun t : ℝ => (f t).re) =ᶠ[𝓝 x] realJet f m := by
        filter_upwards [(Complex.continuous_ofReal.tendsto x).eventually
          hf.eventually_analyticAt] with y hy
        exact ih hy
      rw [iteratedDeriv_succ, heq.deriv_eq]
      exact (hasDerivAt_realJet hf m).deriv

theorem UnitHolomorphic.abs_realJet_le {I : Window} {ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hρ : 0 < ρ) (m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    |realJet f m x| ≤ (m.factorial : ℝ) * (ρ⁻¹) ^ m := by
  apply (Complex.abs_re_le_norm _).trans
  apply norm_iteratedDeriv_le hρ
  · exact hf.analytic.differentiableOn.mono (closedBall_subset_closedTube I ρ hx)
  · intro z hz
    exact hf.norm_le_one z (closedBall_subset_closedTube I ρ hx
      (sphere_subset_closedBall hz))

theorem UnitHolomorphic.abs_iteratedDeriv_le {I : Window} {ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hρ : 0 < ρ) (m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    |iteratedDeriv m (fun t : ℝ => (f t).re) x| ≤
      (m.factorial : ℝ) * (ρ⁻¹) ^ m := by
  rw [iteratedDeriv_realPart (hf.analytic x (real_mem_closedTube I hρ.le hx))]
  exact hf.abs_realJet_le hρ m hx

/-- The loss in passing from a complex radius to the coefficient radius. -/
def radiusLoss (q : ℝ) : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) ^ 2 * q ^ m

theorem summable_radiusLoss {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℕ => ((m : ℝ) + 1) ^ 2 * q ^ m) := by
  have hn : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h0 := summable_geometric_of_norm_lt_one hn
  convert! (h2.add (h1.mul_left 2)).add h0 using 1
  ext m
  ring

theorem radiusLoss_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ radiusLoss q :=
  tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (pow_nonneg hq _))

theorem term_le_radiusLoss {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    ((m : ℝ) + 1) ^ 2 * q ^ m ≤ radiusLoss q :=
  (summable_radiusLoss hq hq1).le_tsum m
    (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg hq _))

/-- The Cauchy bound fits the exact degree-zero manuscript weight. -/
theorem cauchy_bound_le_weight {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) (m : ℕ) :
    (m.factorial : ℝ) * (ρ⁻¹) ^ m ≤
      radiusLoss (ε / ρ) * AxisWeightEstimates.weight ε 0 m := by
  have hρ : 0 < ρ := hε.trans hερ
  have hq : 0 ≤ ε / ρ := (div_pos hε hρ).le
  have hq1 : ε / ρ < 1 := (div_lt_one hρ).mpr hερ
  have hpow : (ε / ρ) ^ m * (ε⁻¹) ^ m = (ρ⁻¹) ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hsq : ((m : ℝ) + 1) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have heq : ((m : ℝ) + 1) ^ 2 * (ε / ρ) ^ m *
      AxisWeightEstimates.weight ε 0 m = (m.factorial : ℝ) * (ρ⁻¹) ^ m := by
    simp only [AxisWeightEstimates.weight, pow_zero, Nat.choose_self,
      Nat.cast_zero, Nat.cast_one, zero_add, one_pow, one_mul, mul_one]
    calc
      ((m : ℝ) + 1) ^ 2 * (ε / ρ) ^ m *
          ((ε⁻¹) ^ m * (m.factorial : ℝ) / ((m : ℝ) + 1) ^ 2) =
          ((ε / ρ) ^ m * (ε⁻¹) ^ m) * (m.factorial : ℝ) := by
            field_simp
      _ = (m.factorial : ℝ) * (ρ⁻¹) ^ m := by rw [hpow, mul_comm]
  rw [← heq]
  exact mul_le_mul_of_nonneg_right (term_le_radiusLoss hq hq1 m)
    (AxisWeightEstimates.weight_pos hε 0 m).le

/-- A coefficient family concentrated at radial degree zero. -/
def degreeZeroJet (f : ℂ → ℂ) (n m : ℕ) (x : ℝ) : ℝ :=
  if n = 0 then realJet f m x else 0

theorem UnitHolomorphic.degreeZeroJet_continuous {I : Window} {ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hρ : 0 < ρ) (n m : ℕ) :
    ContinuousOn (degreeZeroJet f n m) I.interval := by
  change ContinuousOn (fun x => if n = 0 then realJet f m x else 0) I.interval
  by_cases hn : n = 0
  · subst n
    simp only [↓reduceIte]
    intro x hx
    exact (hasDerivAt_realJet
      (hf.analytic x (real_mem_closedTube I hρ.le hx)) m).continuousAt.continuousWithinAt
  · simpa only [degreeZeroJet, ite_eq_right hn] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) I.interval)

theorem UnitHolomorphic.degreeZeroJet_hasDerivWithinAt
    {I : Window} {ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hρ : 0 < ρ) (n m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    HasDerivWithinAt (degreeZeroJet f n m) (degreeZeroJet f n (m + 1) x) I.interval x := by
  change HasDerivWithinAt (fun y => if n = 0 then realJet f m y else 0)
    (if n = 0 then realJet f (m + 1) x else 0) I.interval x
  by_cases hn : n = 0
  · subst n
    simp only [↓reduceIte]
    exact (hasDerivAt_realJet
      (hf.analytic x (real_mem_closedTube I hρ.le hx)) m).hasDerivWithinAt
  · simpa only [degreeZeroJet, ite_eq_right hn] using
      (hasDerivWithinAt_const x I.interval (0 : ℝ))

theorem UnitHolomorphic.degreeZeroJet_bound {I : Window} {ε ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hε : 0 < ε) (hερ : ε < ρ)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    |degreeZeroJet f n m x| ≤
      radiusLoss (ε / ρ) * AxisWeightEstimates.weight ε n m := by
  by_cases hn : n = 0
  · subst n
    simpa only [degreeZeroJet, ↓reduceIte] using
      (hf.abs_realJet_le (hε.trans hερ) m hx).trans (cauchy_bound_le_weight hε hερ m)
  · simp only [degreeZeroJet, ite_eq_right hn, abs_zero]
    exact mul_nonneg (radiusLoss_nonneg (div_nonneg hε.le (hε.trans hερ).le))
      (AxisWeightEstimates.weight_pos hε n m).le

/-- A bounded holomorphic function supplies an actual degree-zero element
of the compatible coefficient Banach space. -/
def UnitHolomorphic.toAxisSpace {I : Window} {ε ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hε : 0 < ε) (hερ : ε < ρ) : AxisSpace I ε :=
  ofJetFamily I (AxisWeightEstimates.weight ε) (AxisWeightEstimates.weight_pos hε)
    (degreeZeroJet f) (hf.degreeZeroJet_continuous (hε.trans hερ))
    (fun n m _ hx => hf.degreeZeroJet_hasDerivWithinAt (hε.trans hερ) n m hx)
    (radiusLoss (ε / ρ)) (radiusLoss_nonneg (div_nonneg hε.le (hε.trans hερ).le))
    (fun n m _ hx => hf.degreeZeroJet_bound hε hερ n m hx)

theorem UnitHolomorphic.norm_toAxisSpace_le {I : Window} {ε ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hε : 0 < ε) (hερ : ε < ρ) :
    ‖hf.toAxisSpace hε hερ‖ ≤ radiusLoss (ε / ρ) := by
  unfold UnitHolomorphic.toAxisSpace
  exact norm_ofJetFamily_le _ _ _ _ _ _ _ _ _

theorem UnitHolomorphic.coefficient_toAxisSpace {I : Window} {ε ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hε : 0 < ε) (hερ : ε < ρ)
    (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I (AxisWeightEstimates.weight ε) (hf.toAxisSpace hε hερ) n x =
      if n = 0 then (f (x : ℂ)).re else 0 := by
  unfold UnitHolomorphic.toAxisSpace
  rw [coefficient_ofJetFamily _ _ _ _ _ _ _ _ _ n hx]
  simp only [degreeZeroJet, realJet, iteratedDeriv_zero]

theorem UnitHolomorphic.jet_toAxisSpace {I : Window} {ε ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hε : 0 < ε) (hερ : ε < ρ)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    jet I (AxisWeightEstimates.weight ε) (hf.toAxisSpace hε hερ).1 n m x =
      if n = 0 then iteratedDeriv m (fun t : ℝ => (f t).re) x else 0 := by
  unfold UnitHolomorphic.toAxisSpace
  rw [jet_ofJetFamily _ _ _ _ _ _ _ _ _ n m hx]
  rw [iteratedDeriv_realPart (hf.analytic x (real_mem_closedTube I (hε.trans hερ).le hx))]
  rfl

/-- The normalized axis exponential, defined on the whole complex plane
but bounded using the common complex neighborhood. -/
def normalizedExp (F : ℂ → ℂ) (Λ C : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((Λ : ℂ) * F z) / (C : ℂ)

/-- One lower bound on `C` supplies all derivative bounds simultaneously.
The upper bound on `Re F` is imposed on the complex tube, not just its real axis. -/
theorem normalizedExp_unitHolomorphic {I : Window} {ρ Λ C M : ℝ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (closedTube I ρ))
    (hM : ∀ z ∈ closedTube I ρ, (F z).re ≤ M)
    (hΛ : 0 ≤ Λ) (hC : Real.exp (Λ * M) ≤ C) :
    UnitHolomorphic I ρ (normalizedExp F Λ C) := by
  have hCpos : 0 < C := (Real.exp_pos _).trans_le hC
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hCpos.ne'
  constructor
  · intro z hz
    unfold normalizedExp
    exact ((analyticAt_const.mul (hF z hz)).cexp).div analyticAt_const hCne
  · intro z hz
    simp only [normalizedExp, norm_div, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hCpos, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    apply (div_le_one hCpos).mpr
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hM z hz) hΛ)).trans hC

/-- Supremum over a fixed compact complex set, used for the literal
normalization threshold `exp(Λ sup Re F)`. -/
def realPartSup (F : ℂ → ℂ) (K : Set ℂ) : ℝ :=
  sSup ((fun z => (F z).re) '' K)

theorem re_le_realPartSup {F : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hF : ContinuousOn F K) {z : ℂ} (hz : z ∈ K) :
    (F z).re ≤ realPartSup F K :=
  le_csSup (hK.bddAbove_image (Complex.continuous_re.comp_continuousOn hF))
    (mem_image_of_mem (fun z => (F z).re) hz)

/-- A compact wider complex neighborhood is enough: every radius-`ρ`
closed disc about a real parameter must lie inside it. -/
theorem normalizedExp_unitHolomorphic_of_compact
    {I : Window} {ρ Λ C : ℝ} {F : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hF : AnalyticOnNhd ℂ F K)
    (hcover : ∀ x ∈ I.interval, closedBall (x : ℂ) ρ ⊆ K)
    (hΛ : 0 ≤ Λ) (hC : Real.exp (Λ * realPartSup F K) ≤ C) :
    UnitHolomorphic I ρ (normalizedExp F Λ C) := by
  have hsub : closedTube I ρ ⊆ K := by
    rintro z ⟨x, hx, hz⟩
    exact hcover x hx hz
  exact normalizedExp_unitHolomorphic (hF.mono hsub)
    (fun z hz => re_le_realPartSup hK hF.continuousOn (hsub hz)) hΛ hC

theorem normalizedExp_re_of_real {F : ℂ → ℂ} {Λ C x : ℝ}
    (hreal : (F (x : ℂ)).im = 0) :
    (normalizedExp F Λ C (x : ℂ)).re = Real.exp (Λ * (F (x : ℂ)).re) / C := by
  have heq : F (x : ℂ) = ((F (x : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  rw [normalizedExp, heq, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
    ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [Complex.ofReal_re]

/-- Uniform degree-zero data for every admissible pair `(Λ,C)`.
The element is constructed from compatible actual derivatives, and its
norm bound depends only on the two radii. -/
theorem uniform_normalizedExp_axisData
    {I : Window} {ε ρ M : ℝ} {F : ℂ → ℂ}
    (hε : 0 < ε) (hερ : ε < ρ)
    (hF : AnalyticOnNhd ℂ F (closedTube I ρ))
    (hM : ∀ z ∈ closedTube I ρ, (F z).re ≤ M)
    (hreal : ∀ x ∈ I.interval, (F (x : ℂ)).im = 0) :
    ∀ Λ : ℝ, 0 ≤ Λ → ∀ C : ℝ, Real.exp (Λ * M) ≤ C →
      ∃ a : AxisSpace I ε,
        ‖a‖ ≤ radiusLoss (ε / ρ) ∧
        (∀ x ∈ I.interval, coefficient I (AxisWeightEstimates.weight ε) a 0 x =
          Real.exp (Λ * (F (x : ℂ)).re) / C) ∧
        (∀ n : ℕ, n ≠ 0 → ∀ x ∈ I.interval,
          coefficient I (AxisWeightEstimates.weight ε) a n x = 0) := by
  intro Λ hΛ C hC
  let hf := normalizedExp_unitHolomorphic hF hM hΛ hC
  refine ⟨hf.toAxisSpace hε hερ, hf.norm_toAxisSpace_le hε hερ, ?_, ?_⟩
  · intro x hx
    rw [hf.coefficient_toAxisSpace hε hερ 0 hx, ite_eq_left rfl]
    exact normalizedExp_re_of_real (hreal x hx)
  · intro n hn x hx
    rw [hf.coefficient_toAxisSpace hε hερ n hx, ite_eq_right hn]

/-- The compact-neighborhood form uses exactly `C ≥ exp(Λ sup Re F)`.
The order is: fix `I, ε, ρ, K, F`, then choose `Λ` and any sufficiently
large `C`; the coefficient norm threshold remains the same. -/
theorem uniform_normalizedExp_axisData_of_compact
    {I : Window} {ε ρ : ℝ} {F : ℂ → ℂ} {K : Set ℂ}
    (hε : 0 < ε) (hερ : ε < ρ)
    (hK : IsCompact K) (hF : AnalyticOnNhd ℂ F K)
    (hcover : ∀ x ∈ I.interval, closedBall (x : ℂ) ρ ⊆ K)
    (hreal : ∀ x ∈ I.interval, (F (x : ℂ)).im = 0) :
    ∀ Λ : ℝ, 0 ≤ Λ → ∀ C : ℝ, Real.exp (Λ * realPartSup F K) ≤ C →
      ∃ a : AxisSpace I ε,
        ‖a‖ ≤ radiusLoss (ε / ρ) ∧
        (∀ x ∈ I.interval, coefficient I (AxisWeightEstimates.weight ε) a 0 x =
          Real.exp (Λ * (F (x : ℂ)).re) / C) ∧
        (∀ n : ℕ, n ≠ 0 → ∀ x ∈ I.interval,
          coefficient I (AxisWeightEstimates.weight ε) a n x = 0) := by
  have hsub : closedTube I ρ ⊆ K := by
    rintro z ⟨x, hx, hz⟩
    exact hcover x hx hz
  exact uniform_normalizedExp_axisData hε hερ (hF.mono hsub)
    (fun z hz => re_le_realPartSup hK hF.continuousOn (hsub hz)) hreal

end NavierStokes.AnalyticCoefficientBounds
